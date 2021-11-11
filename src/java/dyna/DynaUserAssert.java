package dyna;

/**
 * Represent asserts which are from the user's program
 */
public class DynaUserAssert extends DynaUserError {

    public final Object filename;
    public final int line;
    public final String assert_text;
    public final Object assert_rexpr;

    public DynaUserAssert(Object filename, int line, String assert_text, Object assert_rexpr) {
        this.filename = filename;
        this.line = line;
        this.assert_text = assert_text;
        this.assert_rexpr = assert_rexpr;
    }

    public String getMessage() {
        if(filename == null) {
            return "Assert on line " + line + " failed\n" + assert_text;
        } else {
            return "Assert at " + filename.toString() + ":"+line + " failed\n" + assert_text;
        }
    }

}
