package dyna;

import clojure.lang.IFn;

public interface DIterator {

    void iter_run_cb(IFn cb_function);

    // this should reutrn a (lazy) sequence of bindings for the variable
    Object iter_run_iterable();

    // return a lazy sequence over bindings, but this might repeat a value, as
    // this is unconsolidated.  This will allow us to to deal with the case that
    // there is an nil (wild card) binding in the prefix trie

    // the same branch might get returned multiple times also.  So it is
    // ___NOT___ valid to simply sum the multiplicies of what is returned from
    // these branches.  This methods should __ONLY__ be used to get an upper
    // bound on which disjuncts are possible
    Object iter_run_iterable_unconsolidated();

    DIterator iter_bind_value(Object value);

    Object iter_debug_which_variable_bound();

    int iter_estimate_cardinality();
}
