package dyna;

/**
 * Assumptions are controlled in the file assumptions.clj.  An assumption is
 * used to track anything which /might/ change in the future.  An assumption can
 * only transition from a valid to invalid state.  (A new assumption will be
 * created in its place, rather than having a reset mechnism).  If an invalid
 * assumption is used for anything, then an invalid assumption exception will be
 * thrown.  Depending on an invalid assumption is a waste of computation time,
 * hence we want to stop the computation as soon as we have identified that it
 * is invalid.
 */
public class InvalidAssumption extends RuntimeException {

    public InvalidAssumption(String msg) {
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
