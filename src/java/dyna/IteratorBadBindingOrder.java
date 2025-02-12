package dyna;

/**
 * This exception would indicate some kind of error, but it could happen from
 * JITted code which is going to make assumptions about what it can do without
 * necessarily checking with all of the possible combinations first.
 */
public class IteratorBadBindingOrder extends RuntimeException {
    public IteratorBadBindingOrder(String msg) {
        super(msg);
    }

    public IteratorBadBindingOrder() {
        super("Bad binding order for iterator");
    }
}
