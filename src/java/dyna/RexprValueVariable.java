package dyna;

/**
 * An interface which is specific to all things which should be treated like a
 * variable.  The JIT will have its own variables which need to get handled specially
 */
public interface RexprValueVariable extends RexprValue {
}
