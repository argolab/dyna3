package dyna;

import java.util.PriorityQueue;
import java.util.HashSet;

public class DynaAgenda {

    private final PriorityQueue<IDynaAgendaWork> queue = new PriorityQueue<>(100, IDynaAgendaWork.comparator); // the work on the agenda
    private final HashSet<IDynaAgendaWork> queued_work = new HashSet<IDynaAgendaWork>(); // the work
    private long work_processed = 0;
    private long time_processing = 0;

    public DynaAgenda() {}

    public synchronized void push_work(IDynaAgendaWork work) {
        // if we add the same work multiple times, then we are going to ignore it
        if(!queued_work.contains(work)) {
            queue.add(work);
            queued_work.add(work);
        }
    }

    public void process_agenda() throws InterruptedException {
        if(queue.isEmpty())
            return;
        if(print_agenda_running)
            System.err.println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~Running agenda~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        long local_processed = 0;
        long agenda_start_processing = System.currentTimeMillis();
        try {
            while(true) {
                if(Thread.interrupted())
                    throw new InterruptedException();
                //System.out.println("Running work");
                IDynaAgendaWork work;
                synchronized (this) {
                    work = queue.poll();
                    if(work == null) break;
                    queued_work.remove(work);
                }
                work.run();
                local_processed++;
                if(print_progress && local_processed % 5173 == 0) {
                    System.err.print("\rAgenda status, work processed: "+local_processed);
                }
            }
        } finally {
            work_processed += local_processed;
            long time = System.currentTimeMillis() - agenda_start_processing;
            StatusCounters.agenda_processing_time(local_processed, time);
            if(print_agenda_running)
                System.err.println("~~~~~~~~~~~~~~~~Done running agenda, " + local_processed + " work processed in " + time/1000.0 + " seconds~~~~~~~~~~~~~");
        }
    }

    /*
      // This is theory code about how a concurrent system could be implement

      public final int num_threads = System.getProperty("dyna.num_threads") != null ? Integer.parseInt(System.getProperty("dyna.num_threads")) :  Runtime.getRuntime().availableProcessors();

      private final ReentrantReadWriteLock concurrent_work_lock = new ReentrantReadWriteLock();
      private final rwlExecutorService thread_pool = Executors.newCachedThreadPool();
      private void process_agenda_concurrently() throws InterruptedException {
          for(int i = 0; i < num_threads; i++)
              // submit the work into the
      }

      private void run_agenda_from_thread() {
          // this would have to manage the clojure variable dynamic values.  Maybe do something like get the dynamic values from the initial thread
          // and then push those values on all of the worker threads

          while(!is_interrupted) {
              IDynaAgendaWork work;
              synchronized (this) {
                  work = queue.poll();
                  if(work == null) break;
                  queued_work.remove(work);
              }
              // the main idea is that the work could tell us if it is safe to run concurrently.  The memoization values should be able to do that
              // without too much trouble as long as it checks that the relevant values are not modified inbetween the start and finishing of processing
              // other work (such as making new memo tables or other management tasks) would just run single threaded as they would be required to grab
              // the write lock which would block until everything else is taken out
              Lock lock = work.can_run_concurrently() ? concurrent_work_lock.readLock() : concurrent_work_lock.writeLock();
              lock.lock();
              try {
                  work.run();
              } catch (DynaRetryWork err) {
                  // this would put the work back on the agenda
              } finally {
                  lock.unlock();
              }
              local_processed++; // this could be replaced with an atomic counter
              if(print_progress && local_processed % 5173 == 0) {
                System.err.print("\rAgenda status, work processed: "+local_processed);
              }
          }
      }


      void interrupt() {
          is_interrupted = true;  // something which stops it from processing, rather than using thread.interrupted
      }

     */


    public boolean is_done() {
        return queue.isEmpty();
    }

    public synchronized void clear_agenda() {
        // to be only called from the REPL by the user.  This will potentially cause things to break
        queue.clear();
        queued_work.clear();
    }

    public static final boolean print_progress = Boolean.parseBoolean(System.getProperty("dyna.print_agenda_progress", "false"));
    public static final boolean print_agenda_running = Boolean.parseBoolean(System.getProperty("dyna.print_agenda_running", "true"));
    public static final boolean print_agenda_work = Boolean.parseBoolean(System.getProperty("dyna.print_agenda_work", "true"));

}
