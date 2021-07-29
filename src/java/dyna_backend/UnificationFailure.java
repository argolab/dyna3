package dyna_backend;

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

    static final private boolean is_debugging = true;
}
