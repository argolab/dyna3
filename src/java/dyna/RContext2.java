package dyna;

import clojure.lang.IFn;

public interface RContext2 {

    Rexpr2 ctx_get_rexpr();

    Object ctx_get_value(RexprValue2 variable);

    boolean ctx_is_bound_QMARK_(RexprValue2 variable);

    void ctx_set_value_BANG_(RexprValue2 variable, Object value);

    void ctx_add_rexpr_BANG_(Rexpr2 rexpr);

    void ctx_add_context_BANG_(RContext2 other_context);

    Object ctx_all_rexprs();

    Rexpr2 ctx_exit_context(Rexpr2 resulting_rexpr);

    Object ctx_intersect(RContext2 other);

    Object ctx_subtract(RContext2 other);

    Object ctx_scan_through_conjuncts(IFn scan_fn);

    boolean ctx_contains_rexpr_QMARK_(Rexpr2 rexpr);

    // for debugging
    Object ctx_get_inner_values();
    Object ctx_get_all_bindings();

    Object ctx_get_value_map_upto_context(RContext2 parent_context);

}
