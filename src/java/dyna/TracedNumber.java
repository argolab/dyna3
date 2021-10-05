package dyna;

import com.strobel.core.Comparer;

import java.util.Comparator;
import java.util.PriorityQueue;
import java.util.concurrent.Callable;

public final class TracedNumber {

    public final double value;
    public final int height;

    public double accumulated_gradient;
    public final clojure.lang.IFn propagate_back;
    public boolean enqueued_in_backwards_computation = false;


    public double getValue() {
        return value;
    }

    public int getHeight() {
        return height;
    }

    public double getGradient() {
        return accumulated_gradient;
    }

    public void addToGradient(double v) {
        accumulated_gradient += v;
    }

    public TracedNumber(double val, int height, clojure.lang.IFn propagate) {
        value = val;
        this.height = height;
        propagate_back = propagate; // this will be called with the this parameter
        accumulated_gradient = 0;
    }

    @Override
    public String toString() {
        return java.lang.Double.toString(value);
    }

    static final public Comparator<TracedNumber> height_compare = new Comparator<TracedNumber>() {
        @Override
        public int compare(TracedNumber t0, TracedNumber t1) {
            return t0.height - t1.height;
        }
    };

    static public void runBackprop(TracedNumber loss) {
        loss.accumulated_gradient = 1;
        PriorityQueue<TracedNumber> queue = new PriorityQueue<>(loss.getHeight() + 1, height_compare);
        loss.enqueue(queue);
        while(!queue.isEmpty()) {
            TracedNumber t = queue.poll();
            t.propagate_back.invoke(t, queue);
        }
    }

    public void enqueue(PriorityQueue<TracedNumber> q) {
        if(!enqueued_in_backwards_computation) {
            q.add(this);
            enqueued_in_backwards_computation = true;
        }
    }
}
