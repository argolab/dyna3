package dyna;

class InvalidAssumption extends RuntimeException {

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
