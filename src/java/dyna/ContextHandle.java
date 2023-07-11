package dyna;

/**
 * Get the pointer to the current context used by the current thread.  Bypass
 * using clojure's binding as that is going to indirect through its hashmap,
 * where using the java builtin threadlocal should only have a few indirections
 * through pointers/arrays.
 */
public class ContextHandle {
    private ContextHandle() {}

    public static final ThreadLocal<RContext> handle = new ThreadLocal<>();

    public static RContext get() { return handle.get(); }
    public static void set(RContext v) { handle.set(v); }
}
