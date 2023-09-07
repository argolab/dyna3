package dyna;

import clojure.lang.IFn;
import clojure.lang.AFn;
import clojure.lang.RT;
import clojure.lang.Atom;
import clojure.lang.PersistentHashSet;


/**
 *  These are the thread local variables which are tracked/used by a dyna program
 *
 *  This replaces clojure's ^:dynamic using helpers in utils.clj as the
 *  implementation of ^:dynamic is very slow, and indirects through a hash map
 *  every time that it access a thread local variable.
 *
 *  The context is also a thread local variable, but it is handled directly
 *  through the ContextHandle class
 */
@SuppressWarnings("unchecked")
public final class ThreadVar {

    private ThreadVar() {}

    private static final ThreadLocal<ThreadVar> handle = new ThreadLocal() {
            @Override
            protected ThreadVar initialValue() {
                return new ThreadVar();
            }
        };
    public static ThreadVar get() { return handle.get(); }


    // assumption.clj
    public Object current_watcher = null;
    public boolean fast_fail_on_invalid_assumption = false;

    // rexpr.clj
    public Rexpr current_top_level_rexpr = null;
    public Object current_simplify_stack = null;
    public IFn current_simplify_running = null;

    public IFn memoization_make_guesses_handler = new AFn() {
            public Object invoke(Object memo_table, Object variables, Object variable_values) {
                return false;
            }
        };
    public boolean simplify_with_inferences = false;
    public boolean simplify_looking_for_fast_fail_only = false;


    // memoization_v2.clj
    public boolean expand_memoization_placeholder = true;
    public boolean lookup_memoized_values = true;
    public Object memoization_forward_placeholder_bindings = null;

    // rexpr_builtins.clj
    public boolean dollar_free_matches_ground_values = false;

    // rexpr_aggregators_optimized.clj
    public IFn aggregator_op_contribute_value = RT.var("dyna.rexpr-aggregators-optimized", "aggregator-op-contribute-value-default");

    public IFn aggregator_op_additional_constraints = RT.var("dyna.rexpr-aggregators-optimized", "aggregator-op-additional-constraints-default");


    public IFn aggregator_op_saturated = new AFn () {
            public Object invoke(){
                return false;
            }
        };

    public IFn aggregator_op_get_variable_value = RT.var("dyna.base-protocols", "get-value");

    public boolean aggregator_op_should_eager_run_iterators = false;

    // public Object aggregator_active_aggregator = null;
    // public Object aggregator_accumulator = null;
    // public Object aggregator_


    // system.clj
    public boolean auto_run_agenda_before_query = Boolean.parseBoolean(System.getProperty("dyna.auto_run_agenda", "true"));
    //public boolean use_optimized_rexprs = Boolean.parseBoolean(System.getProperty("dyna.optimized_rexprs", "true"));

    public boolean use_optimized_disjunct = true;
    public boolean generate_new_jit_rewrites = false;
    public boolean generate_new_jit_states = false;
    public boolean recursive_transformation_to_jit_state = true;
    public boolean is_generating_jit_rewrite = false;

    public Atom globally_defined_user_term = new Atom(RT.map());
    public Atom user_defined_terms = new Atom(RT.map());
    public Atom user_exported_terms = new Atom(RT.map());
    public Atom imported_files = new Atom(PersistentHashSet.EMPTY);
    public DynaAgenda work_agenda = new DynaAgenda();
    public Atom user_recursion_limit = new Atom(default_recursion_limit);
    public static final int default_recursion_limit = Integer.valueOf(System.getProperty("dyna.recursion_limit", "20"));
    public IFn query_output = RT.var("clojure.core", "println");
    public IFn parser_external_value = new AFn() {
            public Object invoke(Object index) {
                throw new DynaUserError("No external value handler set");
            }
        };
    public Atom dynabase_metadata = new Atom(RT.map());
    public Object dyna_active_system = null;

}
