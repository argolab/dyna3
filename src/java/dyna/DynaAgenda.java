package dyna;

import java.util.PriorityQueue;

public class DynaAgenda {

    private final PriorityQueue<IDynaAgendaWork> queue = new PriorityQueue<>(100, IDynaAgendaWork.comparator);
    private long work_processed = 0;

    public DynaAgenda() {}

    public void push_work(IDynaAgendaWork work) {
        queue.add(work);
    }

    public void process_agenda() {
        while(true) {
            IDynaAgendaWork work = queue.poll();
            if(work == null) break;
            work.run();
            work_processed++;
            if(print_progress && work_processed % 5173 == 0) {
                System.err.print("\rAgenda status, work processed: "+work_processed);
            }
        }
    }

    public final boolean print_progress = Boolean.parseBoolean(System.getProperty("dyna.print_agenda_progress", "false"));
}
