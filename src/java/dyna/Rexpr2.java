package dyna;

import clojure.lang.ILookup; // this is basically things like hash maps etc
import clojure.lang.IFn;

/**
 * The base interface for the R-expr
 */
public interface Rexpr2 {
    Rexpr2 primitive_rexpr();

    Object get_variables();

    Object get_children();

    Object get_argument(int n);

    Object get_argument_name(Object name);

    Object get_arguments();

    Object as_list();

    Object exposed_variables();

    Object get_all_variables_rec();

    Rexpr2 remap_variables(ILookup renaming_map);

    Rexpr2 rewrite_rexpr_children(IFn remap_function);

    Rexpr2 rewrite_rexpr_children_no_simp(IFn remap_function);

    Rexpr2 remap_variables_func(IFn remap_function);

    Rexpr2 remap_variables_handle_hidden(ILookup renaming_map);

    boolean is_constraint_QMARK_();

    String rexpr_name();

    boolean is_empty_rexpr_QMARK_();

    boolean is_non_empty_rexpr_QMARK_();

    Object rexpr_map_function_with_access_path(IFn f);

    Object all_conjunctive_rexprs();

    Object rexpr_jit_info();

    Object check_rexpr_basecases(Object stack);

    Rexpr2 simplify_fast_rexprl(IFn simplify);

    Rexpr2 simplify_inference_rexprl(IFn simplify);

}
