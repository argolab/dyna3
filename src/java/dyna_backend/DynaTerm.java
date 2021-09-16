package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;

public final class DynaTerm {

    public final String name;
    public final Object dynabase;
    public final Object from_file; // a reference to which file this was created in.  This information is used to make a call to an expression, so it is required by the $call reflection which we have in the language
    public final Object arguments;

    private int hashcode_cache = 0;

    public DynaTerm(String name, Object arguments) {
        assert name != null;
        assert clojure_seqable.invoke(arguments) == Boolean.TRUE;
        this.name = name; // .intern(); // it would be nice to intern all of the names.  Then we can just use pointer equality between these different values
        this.dynabase = null;
        this.from_file = null;
        this.arguments = arguments;
    }

    public DynaTerm(String name, Object dynabase, Object from_file, Object arguments) {
        assert name != null;
        assert clojure_seqable.invoke(arguments) == Boolean.TRUE;
        this.name = name; // .intern(); // it would be nice to intern all of the names.  Then we can just use pointer equality between these different values
        this.dynabase = dynabase;
        this.from_file = from_file;
        this.arguments = arguments;
    }

    public String toString() {
        StringBuilder b = new StringBuilder();
        b.append(name);
        if(arguments != null) {
            int count = arity();
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
        // because there are potentially different representations we allow for
        // the arguments (vector, linked list, java array) we want all of these
        // to compare as equal with eachother.  As such, we can't just directly
        // hash the array/vec/etc as those would give different hash code
        // results
        if(hashcode_cache == 0) {
            int h = ((java.lang.Number)clojure_hash.invoke(name)).intValue();
            int count = arity();
            h ^= count;
            for(int i = 0; i < count; i++) {
                h = h * 31 + ((java.lang.Number)clojure_hash.invoke(clojure_get.invoke(arguments, i))).intValue();
            }
            hashcode_cache = h;
        }
        return hashcode_cache;
    }

    public boolean equals(Object other) {
        if(other == this) return true;
        if(!(other instanceof DynaTerm)) return false;
        DynaTerm t = (DynaTerm)other;
        if(t.hashCode() != hashCode() ||
           !name.equals(t.name)) return false;
        int count = arity();
        if(count != t.arity()) return false;
        for(int i = 0; i < count; i++) {
            if(clojure_eq.invoke(clojure_get.invoke(arguments, i),
                                 clojure_get.invoke(t.arguments, i)) != Boolean.TRUE)
                return false;
        }
        return true;
    }

    public int arity() {
        return ((java.lang.Number)clojure_count.invoke(arguments)).intValue();
    }

    public DynaTerm extend_args(Object value) {
        assert(false);
        return null;
    }

    static private final IFn clojure_seqable;
    static private final IFn clojure_hash;
    static private final IFn clojure_count;
    static private final IFn clojure_get;
    static private final IFn clojure_eq;
    static private final IFn clojure_vec;
    static private final IFn clojure_gensym;

    static public final DynaTerm null_term;

    static {
        clojure_seqable = Clojure.var("clojure.core", "seqable?");
        clojure_hash = Clojure.var("clojure.core", "hash");
        clojure_count = Clojure.var("clojure.core", "count");
        clojure_get = Clojure.var("clojure.core", "get");
        clojure_eq = Clojure.var("clojure.core", "=");
        clojure_vec = Clojure.var("clojure.core", "vec");
        clojure_gensym = Clojure.var("clojure.core", "gensym");

        null_term = new DynaTerm("$nil", new Object[]{});
    }

    public static DynaTerm create(String name, Object... args) {
        // if these are making these into a clojure vector, then that means that there is another wrapper around the array which serves as an indirection
        // but having this as a vector will ensure that this does not have the ability to modify the array internally
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
