package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.ILookup;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Static method for use by parser
 */
class ParserUtils {

    private ParserUtils() {}

    static private final IFn clojure_gensym;
    static private final IFn clojure_check_aggregator_defined;


    static {
        clojure_gensym = Clojure.var("clojure.core", "gensym");
        clojure_check_aggregator_defined = Clojure.var("dyna.aggregator", "is-aggregator-defined?");
    }

    public static boolean aggrator_defined(String name) {
        Object result = clojure_check_aggregator_defined.invoke(name);
        return true;
    }

    public static String gensym_variable_name() {
        // this is used by the parser, not really something that "belongs" on
        // the DynaTerm class, but it should be ok

        // this should also get moved off the DynaTerm class to something which
        return clojure_gensym.invoke("$anon_var__").toString();
    }

    private static final AtomicLong colon_line_counter_ = new AtomicLong();
    public static long colon_line_counter() {
        // this returns the counter for the number of times that := rules have
        // appeared in the program this really should not appear on the DynaTerm
        // class as there is no point for it here, so it should get move din the
        // future
        return colon_line_counter_.getAndAdd(1);
    }



}
