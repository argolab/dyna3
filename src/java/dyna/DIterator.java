package dyna;

import clojure.lang.IFn;

public interface DIterator {

    void iter_run_cb(IFn cb_function);

    // this should reutrn a (lazy) sequence of bindings for the variable
    Object iter_run_iterable();

    DIterator iter_bind_value(Object value);

    Object iter_debug_which_variable_bound();

    int iter_estimate_cardinality();
}
