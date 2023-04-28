package dyna;


/**
 * A unification failure means an expresison like `1=2` was in the program.
 * This is equivalent to a `(multiplicity 0)` event.  However, throwing a
 * unification failure can be more efficient than waiting for the `(multiplicity
 * 0)` to processed.
 */
public class UnificationFailure extends RuntimeException {

    public UnificationFailure(String msg) {
        super(msg);
    }

    @Override
    public Throwable fillInStackTrace() {
        // there should be something for checking if the debugger or asserts are enabled
        if(is_debugging) {
            return super.fillInStackTrace();
        } else {
            return null;
        }
    }

    static final private boolean is_debugging = "true".equals(System.getProperty("dyna.debug", "true"));
}
