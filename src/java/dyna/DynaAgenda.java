package dyna;

import java.util.PriorityQueue;

public class DynaAgenda {

    private final PriorityQueue<IDynaAgendaWork> queue = new PriorityQueue<>(100, IDynaAgendaWork.comparator);
    private long work_processed = 0;
    private long time_processing = 0;

    public DynaAgenda() {}

    // public DynaAgenda(DynaAgenda to_copy) {
    //     queue = new PriorityQueue<>(to_copy.queue);
    //     work_processed = to_copy.work_processed;
    //     time_processing = to_copy.time_processing;
    // }

    public void push_work(IDynaAgendaWork work) {
        queue.add(work);
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
                IDynaAgendaWork work = queue.poll();
                if(work == null) break;
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
