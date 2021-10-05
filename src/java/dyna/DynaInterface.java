package dyna;

import java.util.Iterator;

import clojure.java.api.Clojure;
import clojure.lang.IFn;

public interface DynaInterface {


    // high level interface for working with the dyna runtime
    void run_string(String program);
    void run_file(String filename);

    Object run_query(String query);


    // low level interface for directly constructing R-exprs
    Object make_rexpr(String name, Object[] args);
    Object make_variable(String name);
    Object make_constant(Object value);

    // interface to definining user defined terms for an expression.  This will have that
    void add_to_user_defined_term(String name, int arity, Object rexpr);
    void clear_user_defined_term(String name, int artiy);
    void set_user_defined_term(String name, int arity, Object rexpr);
    Object get_user_defined_term(String name, int arity);

    // low level interface for running the evaluation against a program
    Object simplify(Object rexpr);

    String get_term_name(Object term);
    int get_term_arity(Object term);
    Object get_term_argument(Object term, int arg);

    // this would have to have something where it loops over the different values which are possible for an R-expr
    // but there would be multiple variables possible in that expression, so how would that work

    // I suppose that would have to be the result of some query.  In the case that there are variables which are present in the query.
    // We could make it have $0, $1, ..., $n, with it returning an array of objects representing the different assignments to those variables
    // in which case it would have that the iterator would represent which of the expressions could
    Iterator<Object[]> iterate_over_results(Object rexpr);

    public static DynaInterface create() {
        DynaMain.initRuntime();
        return (DynaInterface)Clojure.var("dyna.interface", "get-backend-interface").invoke();
    }
}
