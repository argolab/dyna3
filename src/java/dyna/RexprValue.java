package dyna;

/**
 * This represents things which can have values.  This is variables and constant values
 */
public interface RexprValue {

    Object get_value();

    Object get_value_in_context(RContext ctx);

    RexprValue get_representation_in_context(RContext ctx);

    void set_value_BANG_(Object value);

    boolean is_bound_QMARK_();

    boolean is_bound_in_context_QMARK_(RContext ctx);

    Object all_variables();

}
