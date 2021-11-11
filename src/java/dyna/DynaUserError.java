package dyna;


/**
 * base class for errors which are the result of the user doing something that they shouldn't have done
 */
public class DynaUserError extends RuntimeException {

    public DynaUserError() {}
    public DynaUserError(String msg) { super(msg); }
}
