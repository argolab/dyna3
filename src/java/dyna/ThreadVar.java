package dyna;

/**
 * NOT USED CURRENTLY
 *
 * Move from the clojure thread local bindings, to
 */
@SuppressWarnings("unchecked")
public class ThreadVar {

    private ThreadVar() {}

    private static final ThreadLocal<ThreadVar> handle = new ThreadLocal() {
            @Override
            protected ThreadVar initialValue() {
                return new ThreadVar();
            }
        };
    public static ThreadVar get() { return handle.get(); }



    public Object current_watcher = null;

}
