package dyna;

import java.util.Iterator;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.RT;
import java.net.URL;
import java.net.MalformedURLException;


/**
 * The interface for working with the Dyna runtime
 *
 * Libraries should build against this interface as it should not change (as
 * much as possible).  Other internal implementation details might change in the future
 */
public final class DynaInterface {

    private static final IFn run_string_f;
    private static final IFn run_file_f;
    private static final IFn run_query_f;
    private static final IFn create_system_f;
    private static final IFn is_rexpr_f;
    private static final IFn make_variable_f;
    private static final IFn make_constant_f;
    private static final IFn make_rexpr_f;
    private static final IFn get_rexpr_name_f;
    private static final IFn define_external_function_f;
    //private static final IFn clojure_get;
    private static final IFn clojure_keyword;

    /**
     * Wrap an instance of the DynaSystem.  There can be multiple dyna runtimes
     * instantiated at the same time.  These are created by the method
     * `create_dyna_system` below.  The internals of this are opaque
     */
    public static class DynaSystem {
        final Object system;
        DynaSystem(Object v) { system = v; }
        public boolean equals(Object o) {
            return o instanceof DynaSystem && ((DynaSystem)o).system == system;
        }
        public int hashCode() {
            return System.identityHashCode(system);
        }
        public String toString() {
            return "DynaSystem@" + hashCode();
        }
    }

    /**
     * Wrap an R-expr if returned.  An R-expr represents the internal
     * representation of a dyna program.
     */
    public static class DynaRexpr {
        final Object wrapped;
        DynaRexpr(Object v) { wrapped = v; }
        public boolean equals(Object o) {
            return o instanceof DynaRexpr &&
                (wrapped == null ?
                 ((DynaRexpr)o).wrapped == null :
                 wrapped.equals(((DynaRexpr)o).wrapped));
        }
        public int hashCode () {
            return wrapped == null ? 0 : wrapped.hashCode();
        }
        public String toString() {
            return wrapped == null ? "rexpr_null" : wrapped.toString();
        }
        /**
         * Get a field from an R-expr by name
         */
        public Object get(String fieldName) {
            Object ret = RT.get(wrapped, clojure_keyword.invoke(fieldName));
            if((Boolean)is_rexpr_f.invoke(ret))
                return new DynaRexpr(ret);
            return ret;
        }
        /**
         * Return the name of the R-expr type
         */
        public String type() {
            return wrapped == null ? "rexpr_null" : (String)get_rexpr_name_f.invoke(wrapped);
        }
    }


    // public void runString(String program) { run_string(program); }
    // public void runString(DynaSystem s, String program) { run_string(s, program); }
    public void run_string(String program) { run_string(null, program); }
    public void run_string(DynaSystem s, String program) { run_string(s, program, null); }
    public void run_string(DynaSystem s, String program, Object[] external_values) {
        run_string_f.invoke(s == null ? null : s.system, program, external_values);
    }

    public void run_file(DynaSystem s, String filename) throws MalformedURLException {
        URL cur_dir = new java.io.File(System.getProperty("user.dir")).toURI().toURL();
        URL f;
        if(filename.contains("://")) {
            f = new URL(filename);
        } else {
            f = new URL(cur_dir, filename);
        }
        run_file(s, f);
    }

    public void run_file(DynaSystem s, URL filename) {
        run_file_f.invoke(s == null ? null : s.system, filename);
    }

    public Object run_query(String q) { return run_query(null, q); }
    public Object run_query(DynaSystem s, String query) {
        // this might come back as an R-expr, in which case I suppose that we should wrap it in something
        return run_query(s, query, null);
    }

    public Object run_query(DynaSystem s, String query, Object[] external_values) {
        Object r = run_query_f.invoke(s == null ? null : s.system, query, external_values);
        if(is_rexpr(r)) {
            return new DynaRexpr(r);
        }
        return r;
    }

    public boolean is_rexpr(Object v) {
        return (Boolean)is_rexpr_f.invoke(v);
    }

    public Object make_variable(String name) {
        return make_variable_f.invoke(name);
    }

    public Object make_constant(Object value) {
        return make_constant_f.invoke(value);
    }

    public DynaRexpr make_rexpr(String name, Object[] args) {
        Object[] pargs = new Object[args.length];
        for(int i = 0; i < args.length; i++) {
            if(args[i] instanceof DynaRexpr) {
                pargs[i] = ((DynaRexpr)args[i]).wrapped;
            } else {
                pargs[i] = args[i];
            }
        }
        return new DynaRexpr(make_rexpr_f.invoke(name, pargs));
    }

    /**
     * Define an external function which will be defined globally
     */
    public void define_external_function(DynaSystem sys, String function_name, int function_arity, ExternalFunction func) {
        define_external_function_f.invoke(sys == null ? null : sys.system, function_name, function_arity, func);
    }

    public void define_external_function(DynaSystem sys, String function_name, int function_arity, IFn func) {
        define_external_function(sys, function_name, function_arity, new ExternalFunction () {
                public Object call(Object... args) {
                    return func.applyTo(RT.seq(args));
                }
            });
    }

    /*
    // high level interface for working with the dyna runtime
    void run_string(Object system, String program);
    void run_file(Object system, String filename);

    Object run_query(Object system, String query);


    // low level interface for directly constructing R-exprs
    Object make_rexpr(String name, Object[] args);
    Object make_variable(String name);
    Object make_constant(Object value);

    // // interface to definining user defined terms for an expression.  This will have that
    // void add_to_user_defined_term(Object system, String name, int arity, Object rexpr);
    // void clear_user_defined_term(Object system, String name, int artiy);
    // void set_user_defined_term(Object system, String name, int arity, Object rexpr);
    // Object get_user_defined_term(Object system, String name, int arity);

    // low level interface for running the evaluation against a program
    Object simplify(Object system, Object rexpr);

    String get_term_name(Object term);
    int get_term_arity(Object term);
    Object get_term_argument(Object term, int arg);

    // this would have to have something where it loops over the different values which are possible for an R-expr
    // but there would be multiple variables possible in that expression, so how would that work

    // I suppose that would have to be the result of some query.  In the case that there are variables which are present in the query.
    // We could make it have $0, $1, ..., $n, with it returning an array of objects representing the different assignments to those variables
    // in which case it would have that the iterator would represent which of the expressions could
    //Iterator<Object[]> iterate_over_results(Object rexpr);

    Object create_dyna_sytem();
    */

    public String get_term_name(Object term) {
        if(term instanceof DynaTerm) {
            return ((DynaTerm)term).name;
        }
        return null;
    }

    public int get_term_arity(Object term) {
        if(term instanceof DynaTerm) {
            return ((DynaTerm)term).arity();
        }
        return -1;
    }

    public Object get_term_argument(Object term, int i) {
        if(term instanceof DynaTerm) {
            return ((DynaTerm)term).get(i);
        }
        return null;
    }

    public DynaSystem create_dyna_system() {
        return new DynaSystem(create_system_f.invoke());
    }

    public static DynaInterface getInstance() {
        // there is no need to call this function more than once, all the interfaces which are returned will behave exactly the same
        // DynaMain.initRuntime();
        // Clojure.var("clojure.core", "load").invoke("dyna/public_interface");
        // return (DynaInterface)Clojure.var("dyna.public-interface", "get-backend-interface").invoke();
        return new DynaInterface();
    }

    private DynaInterface() {}

    static {
        DynaMain.initRuntime();
        Clojure.var("clojure.core", "load").invoke("/dyna/public_interface");
        run_string_f = Clojure.var("dyna.public-interface", "run-string");
        run_file_f = Clojure.var("dyna.public-interface", "run-file");
        run_query_f = Clojure.var("dyna.public-interface", "run-query");
        create_system_f = Clojure.var("dyna.public-interface", "create-system");
        is_rexpr_f = Clojure.var("dyna.rexpr", "rexpr?");
        make_variable_f = Clojure.var("dyna.rexpr", "make-variable");
        make_constant_f = Clojure.var("dyna.rexpr", "make-constant");
        make_rexpr_f = Clojure.var("dyna.public-interface", "make-rexpr");
        get_rexpr_name_f = Clojure.var("dyna.base-protocols", "rexpr-name");
        define_external_function_f = Clojure.var("dyna.public-interface", "define-external-function");
        //clojure_get = Clojure.var("clojure.core", "get");
        clojure_keyword = Clojure.var("clojure.core", "keyword");
    }

    public static void main(String[] args) {}
}
