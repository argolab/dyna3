package dyna;

/**
 * This exception is used internally in JITted code when some match expression
 * check fails.  Because the JIT will have to fail and then fall back to some
 * seralization code, that can be handled using nested try/catch blocks where
 * this exception will be thrown.  Given that all of the throw/catches of this
 * exception should be visible inside of the same block of code/compilation
 * unit, it shouldn't have much overhead
 */
public final class DynaJITRuntimeCheckFailed extends RuntimeException {
    public DynaJITRuntimeCheckFailed() {
    }

    @Override
    public Throwable fillInStackTrace() {
        return null;
    }
}
