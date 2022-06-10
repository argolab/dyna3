package dyna;

import java.util.Iterator;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import java.net.URL;
import java.net.MalformedURLException;

public final class DynaInterface {

    public static class DynaSystem {
        final Object system;
        DynaSystem(Object v) { system = v; }
        public boolean equals(Object o) {
            return o instanceof DynaSystem && ((DynaSystem)o).system == system;
        }
    }

    public static class DynaRexpr {
        final Object wrapped;
        DynaRexpr(Object v) { wrapped = v; }
        public boolean equals(Object o) {
            return o instanceof DynaRexpr && ((DynaRexpr)o).wrapped == wrapped;
        }
        public int hashCode () {
            return wrapped.hashCode();
        }
        public String toString() { return wrapped.toString(); }

        // not sure if there should
    }

    private static final IFn run_string_f;
    private static final IFn run_file_f;
    private static final IFn run_query_f;
    private static final IFn create_system_f;
    private static final IFn is_rexpr_f;
    private static final IFn make_variable_f;
    private static final IFn make_constant_f;
    private static final IFn make_rexpr_f;

    public void runString(String program) { run_string(program); }
    public void runString(DynaSystem s, String program) { run_string(s, program); }
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

    public Object run_query(DynaSystem s, String query) {
        // this might come back as an R-expr, in which case I suppose that we should wrap it in something
        Object r = run_query_f.invoke(s == null ? null : s.system, query);
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

    public DynaSystem create_dyna_sytem() {
        return new DynaSystem(create_system_f.invoke());
    }

    public static DynaInterface getInstance() {
        // there is no need to call this function more than once, all the interfaces which are returned will behave exactly the same
        // DynaMain.initRuntime();
        // Clojure.var("clojure.core", "load").invoke("dyna/public_interface");
        // return (DynaInterface)Clojure.var("dyna.public-interface", "get-backend-interface").invoke();
        return new DynaInterface();
    }

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
    }
}
