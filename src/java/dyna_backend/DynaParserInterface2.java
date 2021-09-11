package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;

public class DynaParserInterface2 {

    public static Object make(String name, Object... args) {
        return make_structure.invoke(name, vec.invoke(args));
    }

    public static Object make_arr(String name, Object[] args) {
        return make_structure.invoke(name, vec.invoke(args));
    }

    static final IFn make_structure = Clojure.var("dyna_backend.rexprs", "make-structure");
    static final IFn vec = Clojure.var("clojure.core", "vec");
    private DynaParserInterface2() {}


}
