package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.ILookup;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Static method used by parser
 */
class ParserUtils {

    private ParserUtils() {}

    static private final IFn clojure_gensym;
    static private final IFn clojure_check_aggregator_defined;

    static {
        clojure_gensym = Clojure.var("clojure.core", "gensym");
        clojure_check_aggregator_defined = Clojure.var("dyna.rexpr-aggregators", "is-aggregator-defined?");
    }

    public static boolean aggregator_defined(String name) {
        Object result = clojure_check_aggregator_defined.invoke(name);
        return (Boolean)result;
    }

    public static String gensym_variable_name() {
        return clojure_gensym.invoke("$anon_var__").toString();
    }

    private static final AtomicLong colon_line_counter_ = new AtomicLong();
    public static long colon_line_counter() {
        // this returns the counter for the number of times that := rules have
        // appeared in the program
        return colon_line_counter_.getAndAdd(1);
    }

}
