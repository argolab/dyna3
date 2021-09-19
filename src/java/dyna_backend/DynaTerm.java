package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.ILookup;

public final class DynaTerm implements ILookup {

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
                    Object o = get(i);
                    b.append(o == null ? "null" : o.toString());
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
                // .get does not work with a list
                h = h * 31 + ((java.lang.Number)clojure_hash.invoke(clojure_nth.invoke(arguments, i))).intValue();
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
            if(clojure_eq.invoke(clojure_nth.invoke(arguments, i),
                                 clojure_nth.invoke(t.arguments, i)) != Boolean.TRUE)
                return false;
        }
        return true;
    }

    public int arity() {
        return ((java.lang.Number)clojure_count.invoke(arguments)).intValue();
    }

    public DynaTerm extend_args(Object value) {
        // this makes a new term with something appended to the end of the argument list
        Object args = clojure_vec.invoke(clojure_concat.invoke(arguments, clojure_list.invoke(value)));
        return new DynaTerm(name, dynabase, from_file, args);
    }

    public Object get(int i) {
        return clojure_nth.invoke(arguments, i);
    }

    public Object valAt(Object key) {
        if("name".equals(key)) return name;
        return clojure_nth.invoke(arguments, key);
    }

    public Object valAt(Object key, Object notfound) {
        if("name".equals(key)) return name;
        return clojure_nth.invoke(arguments, key, notfound);
    }

    static private final IFn clojure_seqable;
    static private final IFn clojure_hash;
    static private final IFn clojure_count;
    static private final IFn clojure_nth;
    static private final IFn clojure_eq;
    static private final IFn clojure_vec;
    static private final IFn clojure_gensym;
    static private final IFn clojure_concat;
    static private final IFn clojure_list;

    static public final DynaTerm null_term;

    static {
        clojure_seqable = Clojure.var("clojure.core", "seqable?");
        clojure_hash = Clojure.var("clojure.core", "hash");
        clojure_count = Clojure.var("clojure.core", "count");
        clojure_nth = Clojure.var("clojure.core", "nth");
        clojure_eq = Clojure.var("clojure.core", "=");
        clojure_vec = Clojure.var("clojure.core", "vec");
        clojure_gensym = Clojure.var("clojure.core", "gensym");
        clojure_concat = Clojure.var("clojure.core", "concat");
        clojure_list = Clojure.var("clojure.core", "list");

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

    public static DynaTerm make_list(Object arr) {
        DynaTerm ret = DynaTerm.null_term;
        final int cnt = ((java.lang.Number)clojure_count.invoke(arr)).intValue();
        for(int i = cnt - 1; i >= 0; i--) {
            ret = DynaTerm.create(".", clojure_nth.invoke(arr, i), ret);
        }
        return ret;
    }

    public Object list_to_vec() {
        // this has to construct a clojure vector from a dyna linked list object
        int count = 0;
        DynaTerm s = this;
        while(s.name.equals(".")) {
            count++;
            Object v = s.get(1);
            if(v == null || !(v instanceof DynaTerm)) return null; // the structure is not what we expect
            s = (DynaTerm)v;
        }
        if(!s.equals(null_term)) return null; // not the structure that we expect
        Object[] tmp = new Object[count];
        s = this;
        for(int i = 0; i < count; i++) {
            tmp[i] = s.get(0);
            s = (DynaTerm)s.get(1);
        }
        // vec is going to alias java arrays?  So this should just keep a reference to the above array rather than copying it?
        return clojure_vec.invoke(tmp);
    }
}
