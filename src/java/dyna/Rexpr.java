package dyna;

import clojure.lang.ILookup; // this is basically things like hash maps etc
import clojure.lang.IFn;

/**
 * The base interface for the R-expr
 */
public interface Rexpr {
    Rexpr primitive_rexpr();

    //Rexpr primitive_rexpr_jit_placeholder();

    Object get_variables();

    Object get_children();

    Object get_argument(int n);

    Object get_argument_name(Object name);

    Object get_arguments();

    Object as_list();

    Object exposed_variables();

    Object get_all_variables_rec();

    Rexpr remap_variables(ILookup renaming_map);

    Rexpr rewrite_rexpr_children(IFn remap_function);

    Rexpr rewrite_rexpr_children_no_simp(IFn remap_function);

    Rexpr remap_variables_func(IFn remap_function);

    Rexpr remap_variables_handle_hidden(ILookup renaming_map);

    Object rewrite_all_args(IFn remap_function);

    boolean is_constraint_QMARK_();

    Object variable_functional_dependencies();

    Object rexpr_name();

    boolean is_empty_rexpr_QMARK_();

    boolean is_non_empty_rexpr_QMARK_();

    Object rexpr_map_function_with_access_path(IFn f);

    Object all_conjunctive_rexprs();

    Object rexpr_jit_info();

    int rexpr_jittype_hash();

    Object check_rexpr_basecases(Object stack);

    SimplifyRewriteCollection rexpr_simplify_fast_collection();

    SimplifyRewriteCollection rexpr_simplify_construct_collection();

    SimplifyRewriteCollection rexpr_simplify_inference_collection();

    SimplifyRewriteCollection rexpr_jit_compilation_step_collection();
}
