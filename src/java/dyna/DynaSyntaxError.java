package dyna;

public class DynaSyntaxError extends DynaUserError {

    public DynaSyntaxError() {super("Syntax Error");}
    public DynaSyntaxError(String msg) { super(msg); }
    public DynaSyntaxError(String msg, Exception cause) { super(msg, cause); }

}
