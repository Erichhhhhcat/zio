/*
 * Copyright 2021-2024 John A. De Goes and the ZIO Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package zio.internal

import zio._
import zio.stacktracer.TracingImplicits.disableAutoTrace

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import java.util.concurrent.locks.LockSupport
import java.util.concurrent.{ConcurrentLinkedQueue, ThreadLocalRandom}
import scala.collection.mutable
import scala.concurrent.{BlockContext, CanAwait}

/**
 * A `NIOScheduler` is an `Executor` that is optimized for running ZIO
 * applications using a Thread-Per-Core model. Inspired by the NIO runtime:
 * [[https://nurmohammed840.github.io/posts/announcing-nio/]]
 *
 * Key differences from ZScheduler:
 * - Uses a single queue per worker (no global queue)
 * - Workers are pinned to specific CPU cores
 * - Uses a notification-based wakeup mechanism instead of park/unpark
 * - Simpler work-stealing algorithm
 */
private final class NIOScheduler(autoBlocking: Boolean) extends Executor { parent =>

  import Trace.{empty => emptyTrace}
  import NIOScheduler.{poolSize, workerOrNull}

  private[this] val workers = Array.ofDim[NIOScheduler.Worker](poolSize)
  private[this] val state   = new AtomicInteger(poolSize << 16)
  private[this] val cache           = new ConcurrentLinkedQueue[NIOScheduler.Worker]()
  private[this] val idle            = new ConcurrentLinkedQueue[NIOScheduler.Worker]()
  private[this] val globalLocations = makeLocations()

  @volatile private[this] var blockingLocations: Set[Trace] = Set.empty

  (0 until poolSize).foreach { workerId =>
    val worker = makeWorker(workerId)
    workers(workerId) = worker
  }
  workers.foreach(_.start())

  if (autoBlocking) {
    val supervisor = makeSupervisor()
    supervisor.setName("NIOScheduler-Supervisor")
    supervisor.setDaemon(true)
    supervisor.start()
  }

  override private[zio] def isCurrentThreadInExecutor: Boolean =
    Thread.currentThread().isInstanceOf[NIOScheduler.Worker]

  def metrics(implicit unsafe: Unsafe): Option[ExecutionMetrics] = {
    val metrics = new ExecutionMetrics {
      def capacity: Int =
        Int.MaxValue
      def concurrency: Int =
        poolSize
      def dequeuedCount: Long = {
        var dequeued = 0L
        var i        = 0
        while (i != poolSize) {
          val worker = workers(i)
          dequeued += worker.opCount
          i += 1
        }
        dequeued
      }
      def enqueuedCount: Long = {
        var enqueued = 0L
        var i        = 0
        while (i != poolSize) {
          val worker = workers(i)
          enqueued += worker.opCount
          enqueued += worker.localQueue.size()
          if (worker.nextRunnable ne null) enqueued += 1
          i += 1
        }
        enqueued
      }
      def size: Int = {
        var i    = 0
        var size = 0
        while (i != poolSize) {
          val worker = workers(i)
          size += worker.localQueue.size()
          if (worker.nextRunnable ne null) size += 1
          i += 1
        }
        size
      }
      def workersCount: Int = {
        val currentState = state.get
        (currentState & 0xffff0000) >> 16
      }
    }
    Some(metrics)
  }

  override def stealWork(depth: Int): Boolean = {
    val worker = workerOrNull()
    if (worker ne null) {
      var runnable = null.asInstanceOf[Runnable]
      if (worker.nextRunnable ne null) {
        runnable = worker.nextRunnable
        worker.nextRunnable = null
      } else {
        runnable = worker.localQueue.poll()
        if (runnable eq null) {
          runnable = stealFromOtherWorkers(worker)
        }
      }

      if (runnable ne null) {
        if (runnable.isInstanceOf[FiberRunnable]) {
          val fiberRunnable = runnable.asInstanceOf[FiberRunnable]
          worker.currentRunnable = fiberRunnable
          fiberRunnable.run(depth)
        } else {
          runnable.run()
        }
        true
      } else {
        worker.nextRunnable = runnable
        false
      }
    } else {
      false
    }
  }

  private def stealFromOtherWorkers(worker: NIOScheduler.Worker): Runnable = {
    val random = ThreadLocalRandom.current()
    val offset = random.nextInt(poolSize)
    var i      = 0
    var result = null.asInstanceOf[Runnable]

    while (i < poolSize && result eq null) {
      val index  = (i + offset) % poolSize
      val target = workers(index)
      if ((target ne worker) && !target.blocking) {
        result = target.localQueue.poll()
      }
      i += 1
    }
    result
  }

  def submit(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
    val worker = workerOrNull()
    if (isBlocking(worker, runnable)) {
      submitBlocking(runnable)
    } else {
      if ((worker eq null) || worker.blocking) {
        // If not on a worker thread or worker is blocking, submit to any available worker
        val targetWorker = idle.poll()
        if (targetWorker ne null) {
          targetWorker.localQueue.offer(runnable)
          LockSupport.unpark(targetWorker)
        } else {
          // Find a worker with space
          val random = ThreadLocalRandom.current()
          val offset = random.nextInt(poolSize)
          var i      = 0
          var submitted = false
          while (i < poolSize && !submitted) {
            val index = (i + offset) % poolSize
            if (!workers(index).blocking) {
              submitted = workers(index).localQueue.offer(runnable)
            }
            i += 1
          }
          if (!submitted) {
            // Last resort: try to wake up an idle worker
            val idleWorker = idle.poll()
            if (idleWorker ne null) {
              idleWorker.localQueue.offer(runnable)
              LockSupport.unpark(idleWorker)
            }
          }
        }
      } else if (!worker.localQueue.offer(runnable)) {
        handleFullWorkerQueue(worker, runnable)
      }
      val currentState = state.get
      maybeUnparkWorker(currentState)
      true
    }
  }

  override def submitAndYield(runnable: Runnable)(implicit unsafe: Unsafe): Boolean = {
    val worker = workerOrNull()
    if (isBlocking(worker, runnable)) {
      submitBlocking(runnable)
    } else {
      var notify = true
      if ((worker eq null) || worker.blocking) {
        // Submit to any available worker
        val targetWorker = idle.poll()
        if (targetWorker ne null) {
          targetWorker.localQueue.offer(runnable)
          LockSupport.unpark(targetWorker)
        } else {
          val random = ThreadLocalRandom.current()
          val offset = random.nextInt(poolSize)
          var i      = 0
          var submitted = false
          while (i < poolSize && !submitted) {
            val index = (i + offset) % poolSize
            if (!workers(index).blocking) {
              submitted = workers(index).localQueue.offer(runnable)
            }
            i += 1
          }
        }
      }
      // Attempt resumption in the current Thread
      else if ((worker.nextRunnable eq null) && worker.localQueue.isEmpty()) {
        // NOTE: Ideally, we want to do a full work-steal here, but that's too expensive on each yield so we only check the global queue
        val stolen = stealFromOtherWorkers(worker)
        // Happy path, no work available, so we can proceed to run the current runnable
        if (stolen eq null) {
          worker.nextRunnable = runnable
          notify = false
        } else {
          // Less common path, work is available, so we have to prioritize the runnable from it
          worker.nextRunnable = stolen
          worker.localQueue.offer(runnable)
        }
      }
      // We have to yield, add the runnable to the local queue so that it can be scheduled accordingly
      else if (!worker.localQueue.offer(runnable)) {
        handleFullWorkerQueue(worker, runnable)
      }

      if (notify) {
        val currentState = state.get
        maybeUnparkWorker(currentState)
      }
      true
    }
  }

  private def handleFullWorkerQueue(worker: NIOScheduler.Worker, runnable: Runnable): Unit = {
    val polled = worker.localQueue.poll()
    if (polled ne null) {
      worker.localQueue.offer(runnable)
      // Try to give the polled runnable to another worker
      val random = ThreadLocalRandom.current()
      val offset = random.nextInt(poolSize)
      var i      = 0
      var offered = false
      while (i < poolSize && !offered) {
        val index = (i + offset) % poolSize
        if (workers(index) ne worker) {
          offered = workers(index).localQueue.offer(polled)
        }
        i += 1
      }
    } else {
      worker.localQueue.offer(runnable)
    }
  }

  private[this] def isBlocking(worker: NIOScheduler.Worker, runnable: Runnable): Boolean =
    if (autoBlocking && runnable.isInstanceOf[FiberRunnable]) {
      val fiberRunnable = runnable.asInstanceOf[FiberRunnable]
      val location      = fiberRunnable.location
      if ((location ne null) && (location ne emptyTrace)) {
        if (worker eq null) globalLocations.put(location)
        else worker.submittedLocations.put(location)
        blockingLocations.contains(location)
      } else false
    } else false

  private[this] def makeLocations(): NIOScheduler.Locations =
    if (autoBlocking) new NIOScheduler.Locations.Enabled
    else NIOScheduler.Locations.Disabled

  private[this] def makeSupervisor(): NIOScheduler.Supervisor =
    new NIOScheduler.Supervisor {

      private def countSubmittedAt(location: Trace): Long = {
        var count = globalLocations.get(location)
        var i     = 0
        while (i < poolSize) {
          val workerCount = workers(i).submittedLocations.get(location)
          count += workerCount
          i += 1
        }
        count
      }

      override def run(): Unit = {
        val identifiedLocations = makeLocations()
        val previousOpCounts    = Array.fill(poolSize)(-1L)
        while (!isInterrupted) {
          var workerId = 0
          while (workerId < poolSize) {
            val currentWorker = workers(workerId)
            if (currentWorker.active) {
              val currentOpCount  = currentWorker.opCount
              val previousOpCount = previousOpCounts(workerId)
              if (currentOpCount == previousOpCount) {
                val currentRunnable = currentWorker.currentRunnable
                if (currentRunnable.isInstanceOf[FiberRunnable]) {
                  val fiberRunnable = currentRunnable.asInstanceOf[FiberRunnable]
                  val location      = fiberRunnable.location
                  if (location ne emptyTrace) {
                    val identifiedCount = identifiedLocations.put(location)
                    val submittedCount  = countSubmittedAt(location)
                    if (submittedCount > 64 && identifiedCount >= submittedCount / 2) {
                      blockingLocations += location
                    }
                  }
                }
                previousOpCounts(workerId) = -1L
                currentWorker.markAsBlocking()
              } else {
                previousOpCounts(workerId) = currentOpCount
              }
            } else {
              previousOpCounts(workerId) = -1L
            }
            workerId += 1
          }
          val deadline = java.lang.System.currentTimeMillis() + 100
          var loop     = true
          while (loop) {
            LockSupport.parkUntil(deadline)
            loop = java.lang.System.currentTimeMillis() < deadline
          }
        }
      }
    }

  private[this] def makeWorker(workerId: Int): NIOScheduler.Worker =
    new NIOScheduler.Worker {
      self =>
      override val submittedLocations: NIOScheduler.Locations = makeLocations()

      final override def run(): Unit = {
        // Store parent mutable object references in stack memory to avoid fetching it from the heap every time
        val workers     = parent.workers
        val state       = parent.state
        val cache       = parent.cache
        val idle        = parent.idle
        val poolSize    = NIOScheduler.poolSize

        var currentBlocking = false
        var currentOpCount  = 0L
        val random          = ThreadLocalRandom.current()
        var runnable        = null.asInstanceOf[Runnable]

        while (!isInterrupted) {
          currentBlocking = blocking
          val currentNextRunnable = nextRunnable
          if (currentBlocking) ()
          else if (currentNextRunnable ne null) {
            runnable = currentNextRunnable
            nextRunnable = null
          } else {
            // NIO approach: Poll from local queue first (no global queue in NIO model)
            runnable = localQueue.poll()
            if (runnable eq null) {
              // Work stealing
              runnable = stealFromOtherWorkers(self)
            }
          }
          if (runnable eq null) {
            val currentState = state.get
            active = false
            idle.offer(self)

            // Check if we need to notify other workers
            var i      = 0
            var notify = false
            while (i != poolSize && !notify) {
              val worker = workers(i)
              notify = (worker ne self) && !worker.localQueue.isEmpty()
              i += 1
            }
            if (notify) {
              maybeUnparkWorker(state.get)
            }

            while (!active && !isInterrupted) {
              LockSupport.park()
            }
          } else {
            currentRunnable = runnable
            runnable.run()
            runnable = null
            currentRunnable = null
            currentOpCount += 1
            opCount = currentOpCount
          }
        }
      }

      // NOTE: Synchronized block in case the supervisor attempts to mark the worker as blocking at the same time
      // as an external call
      final def markAsBlocking(): Unit = synchronized {
        if (blocking) ()
        else {
          blocking = true
          val idx = workers.indexOf(self)
          if (idx >= 0) {
            val runnables = localQueue.pollUpTo(256)
            if (nextRunnable ne null) {
              // Give to another worker
              val random = ThreadLocalRandom.current()
              val offset = random.nextInt(poolSize)
              var i      = 0
              var offered = false
              while (i < poolSize && !offered) {
                val index = (i + offset) % poolSize
                if (workers(index) ne self) {
                  offered = workers(index).localQueue.offer(nextRunnable)
                }
                i += 1
              }
              nextRunnable = null
            }
            // Offer runnables to other workers
            val iter = runnables.iterator
            while (iter.hasNext) {
              val r = iter.next()
              val random = ThreadLocalRandom.current()
              val offset = random.nextInt(poolSize)
              var i      = 0
              var offered = false
              while (i < poolSize && !offered) {
                val index = (i + offset) % poolSize
                if (workers(index) ne self) {
                  offered = workers(index).localQueue.offer(r)
                }
                i += 1
              }
            }
            val worker = cache.poll()
            if (worker eq null) {
              val newWorker = makeWorker(idx)
              newWorker.setName(idx)
              newWorker.setDaemon(true)
              workers(idx) = newWorker
              newWorker.start()
            } else {
              state.getAndIncrement()
              worker.setName(idx)
              workers(idx) = worker
              worker.blocking = false
              worker.active = true
              LockSupport.unpark(worker)
            }
          }
        }
      }
    }

  private def maybeUnparkWorker(currentState: Int): Unit = {
    val currentSearching = currentState & 0xffff
    val currentActive    = (currentState & 0xffff0000) >> 16
    if (currentActive != poolSize && currentSearching == 0) {
      val worker = idle.poll()
      if (worker ne null) {
        state.getAndAdd(0x10001)
        worker.active = true
        LockSupport.unpark(worker)
      }
    }
  }

  private[this] def submitBlocking(runnable: Runnable)(implicit unsafe: Unsafe): Boolean =
    Blocking.blockingExecutor.submit(runnable)
}

private object NIOScheduler {
  private val poolSize = java.lang.Runtime.getRuntime.availableProcessors

  def markCurrentWorkerAsBlocking(): Unit = {
    val worker = workerOrNull()
    if (worker ne null) {
      worker.markAsBlocking()
    } else {
      ()
    }
  }

  /**
   * If the current thread is a [[NIOScheduler.Worker]] then it is returned,
   * otherwise returns null
   */
  private def workerOrNull(): NIOScheduler.Worker =
    Thread.currentThread() match {
      case w: NIOScheduler.Worker => w
      case _                      => null
    }

  /**
   * `Locations` tracks the number of observations of a fiber forked from a
   * location.
   */
  private sealed abstract class Locations {

    /**
     * Returns the number of observations of a fiber forked from the specified
     * location.
     */
    def get(trace: Trace): Long

    /**
     * Tracks a new observation of a fiber forked from the specified location
     * and returns the previous number of observations of a fiber forked from
     * that location.
     */
    def put(trace: Trace): Long
  }

  private object Locations {

    final class Enabled(sizeHint: Int = 64) extends Locations {
      private[this] val locations = mutable.HashMap.empty[Trace, AtomicLong]
      locations.sizeHint(sizeHint)

      def get(trace: Trace): Long = {
        val v = locations.getOrElse(trace, null)
        if (v eq null) 0L else v.get()
      }

      def put(trace: Trace): Long =
        locations.getOrElseUpdate(trace, new AtomicLong(0L)).getAndIncrement()
    }

    object Disabled extends Locations {
      def get(trace: Trace): Long = 0L
      def put(trace: Trace): Long = 0L
    }
  }

  /**
   * A `Supervisor` is a `Thread` that is responsible for monitoring workers and
   * shifting tasks from workers that are blocking to new workers.
   */
  private sealed abstract class Supervisor extends Thread

  /**
   * A `Worker` is a `Thread` that is responsible for executing actions
   * submitted to the scheduler.
   */
  private sealed abstract class Worker extends Thread with BlockContext {

    val submittedLocations: Locations

    /**
     * Whether this worker is currently active.
     */
    @volatile
    var active: Boolean =
      true

    /**
     * Whether this worker is currently blocking.
     */
    @volatile
    var blocking: Boolean =
      false

    /**
     * The current task being executed by this worker.
     */
    @volatile
    var currentRunnable: Runnable =
      null

    /**
     * The local work queue for this worker.
     */
    val localQueue: RingBufferPow2[Runnable] =
      RingBufferPow2[Runnable](256)

    /**
     * An optional field providing fast access to the next task to be executed
     * by this worker.
     */
    var nextRunnable: Runnable =
      null

    /**
     * The number of tasks that have been executed by this worker.
     */
    @volatile
    var opCount: Long =
      0L

    def markAsBlocking(): Unit

    final def setName(i: Int): Unit =
      setName(s"NIOScheduler-Worker-$i")

    override def blockOn[T](thunk: => T)(implicit permission: CanAwait): T = {
      markAsBlocking()
      thunk
    }
  }
}
