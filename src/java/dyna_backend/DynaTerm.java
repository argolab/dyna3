package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;

public final class DynaTerm {

    public final String name;
    public final Object dynabase;
    public final Object arguments;

    private int hashcode_cache = 0;

    public DynaTerm(String name, Object arguments) {
        assert name != null;
        assert is_seqable.invoke(arguments) == Boolean.TRUE;
        this.name = name; // .intern(); // it would be nice to intern all of the names.  Then we can just use pointer equality between these different values
        this.arguments = arguments;
        this.dynabase = null;
    }

    public DynaTerm(String name, Object dynabase, Object arguments) {
        assert name != null;
        assert is_seqable.invoke(arguments) == Boolean.TRUE;
        this.name = name; // .intern(); // it would be nice to intern all of the names.  Then we can just use pointer equality between these different values
        this.dynabase = dynabase;
        this.arguments = arguments;
    }

    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append(name);
        if(arguments != null) {
            int count = ((java.lang.Number)clojure_count.invoke(arguments)).intValue();
            if(count > 0) {
                b.append("(");
                for(int i = 0; i < count; i++) {
                    if(i != 0) b.append(", ");
                    b.append(clojure_get.invoke(arguments, i).toString());
                }
                b.append(")");
            }
        }
        return b.toString();
    }

    public int hashCode() {
        if(hashcode_cache == 0) {
            hashcode_cache =
                ((java.lang.Number)clojure_hash.invoke(name)).intValue() * 11 +
                ((java.lang.Number)clojure_hash.invoke(arguments)).intValue();
        }
        return hashcode_cache;
    }

    public boolean equals(Object other) {
        if(!(other instanceof DynaTerm)) return false;
        DynaTerm t = (DynaTerm)other;
        return t.hashCode() == hashCode() && name.equals(t.name) && clojure_eq.invoke(arguments, t.arguments) == Boolean.TRUE;
    }

    static private final IFn is_seqable;
    static private final IFn clojure_hash;
    static private final IFn clojure_count;
    static private final IFn clojure_get;
    static private final IFn clojure_eq;
    static private final IFn clojure_vec;
    static private final IFn clojure_gensym;
    static public final DynaTerm null_term;

    static {
        is_seqable = Clojure.var("clojure.core", "seqable?");
        clojure_hash = Clojure.var("clojure.core", "hash");
        clojure_count = Clojure.var("clojure.core", "count");
        clojure_get = Clojure.var("clojure.core", "get");
        clojure_eq = Clojure.var("clojure.core", "=");
        clojure_vec = Clojure.var("clojure.core", "vec");
        clojure_gensym = Clojure.var("clojure.core", "gensym");

        null_term = new DynaTerm("$nil", new Object[]{});
    }

    public static DynaTerm create(String name, Object... args) {
        return new DynaTerm(name, clojure_vec.invoke(args));
    }

    public static DynaTerm create_arr(String name, Object args) {
        // args just needs to be something that can be passed to clojure's `(vec args)`
        // so this can be an array or arraylist etc
        return new DynaTerm(name, clojure_vec.invoke(args));
    }

    public static Object gensym_variable_name() {
        return clojure_gensym.invoke("$runtime_var_");
    }
}
