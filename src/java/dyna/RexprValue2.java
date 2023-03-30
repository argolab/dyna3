package dyna;

/**
 * This represents things which can have values.  This is variables and constant values
 */
public interface RexprValue2 {

    Object get_value();

    Object get_value_in_context(RContext2 ctx);

    RexprValue2  get_representation_in_context(RContext2 ctx);

    void set_value_BANG_(Object value);

    boolean is_bound_QMARK_();

    boolean is_bound_in_context_QMARK_(RContext2 ctx);

    Object all_variables();

}
