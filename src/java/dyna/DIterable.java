package dyna;

public interface DIterable {
    // return a set of which variables this iterator will bind
    Object iter_what_variables_bound();

    // return a list of different valid binding orders
    // the list inside should be order.
    Object iter_variable_binding_order();

    DIterator iter_create_iterator(Object which_binding);
}
