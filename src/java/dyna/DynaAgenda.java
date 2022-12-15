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

    public void process_agenda() {
        if(queue.isEmpty())
            return;
        System.err.println("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~Running agenda~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~");
        long local_processed = 0;
        long agenda_start_processing = System.currentTimeMillis();
        try {
            while(true) {
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
            System.err.println("~~~~~~~~~~~~~~~~Done running agenda, " + local_processed + " work processed in " + time/1000.0 + " seconds~~~~~~~~~~~~~");
        }
    }

    public final boolean print_progress = Boolean.parseBoolean(System.getProperty("dyna.print_agenda_progress", "false"));
}
