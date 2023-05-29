package dyna;

/**
 * This exception is used internally in JITted code when some check fail.
 */
public class DynaJITRunningCheckFailed extends RuntimeException {
    public DynaJITRunningCheckFailed() {
    }

    @Override
    public Throwable fillInStackTrace() {
        return null;
    }
}
