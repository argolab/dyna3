package dyna;

import java.util.Comparator;

interface IDynaAgendaWork extends Runnable {

    public void run();

    public float priority();

    public final static Comparator<IDynaAgendaWork> comparator =
        new Comparator<IDynaAgendaWork> () {
            public int compare(IDynaAgendaWork o1, IDynaAgendaWork o2) {
                float a = o1.priority(), b = o2.priority();
                if(a == b) return 0;
                if(a < b) return -1;
                else return 1;
            }
            public boolean equals(IDynaAgendaWork o1, IDynaAgendaWork o2) { return o1 == o2; }
        };

}
