package dyna;

import clojure.lang.IFn;

/**
 * Interface for the context passed around at runtime.  This tracks conjunctive
 * R-exprs and bindings to variables.
 */
public interface RContext {

    Rexpr ctx_get_rexpr();

    Object ctx_get_value(RexprValue variable);

    boolean ctx_is_bound_QMARK_(RexprValue variable);

    void ctx_set_value_BANG_(RexprValue variable, Object value);

    void ctx_add_rexpr_BANG_(Rexpr rexpr);

    void ctx_add_context_BANG_(RContext other_context);

    Object ctx_all_rexprs();

    Rexpr ctx_exit_context(Rexpr resulting_rexpr);

    Object ctx_intersect(RContext other);

    Object ctx_subtract(RContext other);

    Object ctx_scan_through_conjuncts(IFn scan_fn);

    boolean ctx_contains_rexpr_QMARK_(Rexpr rexpr);

    // for debugging
    Object ctx_get_inner_values();
    Object ctx_get_all_bindings();

    Object ctx_get_value_map_upto_context(RContext parent_context);

}
