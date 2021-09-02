package dyna_backend;

/**
 * This is the interface that the parser uses to generate R-exprs and load them
 * into the main runtime The parser interface will have to track the current
 * "state" of which conjunctive R-exprs have been constructed so far.  Most of
 * the expressions in the surface language are "value based" in that they will
 * return some value.  Which means that a lot of this interface is working over
 * references to variables or constant values
 */
interface DynaParserInterface {
    Object make_rexpr(String name, Object... args); // returns an R-expr
    Object make_rexpr_add(String name, Object... args); // Returns an R-expr

    Object make_variable(String name);  // Returns a variable-value
    Object make_unnamed_variable();  // Returns a variable-value
    Object make_constant(Object value);  // Returns a variable-value
    Object make_call(String user_functor_name, Object args_values_array);  // Returns a variable-value
    Object make_structure(String user_structure_name, Object args_values_array);  // Returns a variable-value

    void unify_with_true(Object value);

    DynaParserInterface copy_interface();

    void set_atom(String name, Object args_values_array, String aggregator_name);
    void construct_atom(Object value);
}
