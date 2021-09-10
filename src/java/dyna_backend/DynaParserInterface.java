package dyna_backend;

import java.util.Set;
import java.util.HashSet;
import java.util.Arrays;

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
    Object make_call_with_dynabase(Object dynabase_value, String user_functor_name, Object args_values_array);
    Object make_structure(String user_structure_name, Object args_values_array);  // Returns a variable-value

    void unify_with_true(Object value);

    DynaParserInterface copy_interface();

    void start_new_atom();
    void start_new_annon_atom();
    void finish_atom();
    Object finish_annon_atom();
    void set_atom_name(String name);
    void set_atom_args(Object args_values_array);
    void set_atom_aggregator(String aggregator_name);
    void set_atom_result_variable(Object result_value);


    void start_new_dynabase();
    void set_dynabase_inherits_variable(Object parent_dynabase_value);
    Object get_dynabase_construct_variable();
    //void start_new_dynabase_inherits(Object parent_dynabase_value);
    void finish_dynabase();

    // this is used in the case that something is defined as `foo.bar(123) = 99`, which is rewritten as `bar(123) = 99 for $self=foo` so the result of `foo` needs to be become unified with the self variable rather than having this
    void set_dynabase_self_variable(Object self_variable);


    //String create_annon_atom();

    // void set_atom(String name, Object args_values_array, String aggregator_name);
    // void construct_atom(Object value);

    public static DynaParserInterface create() {
        // there is probably no use for this, as we would just be calling which of the
        try {
            return (DynaParserInterface)Class.forName("dyna_backend.DynaParserInterfaceImpl").newInstance();
        } catch(ClassNotFoundException|InstantiationException|IllegalAccessException e) {
            return null;
        }
    }


    final public static Set<String> quote_function_names = new HashSet<String>(Arrays.asList("$priority", "$key"));
}
