package dyna;

/**
 * CURRENTLY NOT USED
 *
 * thinking that there are some things which might as well become deferred and
 * wait until they are ground.  For example, in the case of a dynabase, there is
 * not really much that we can do if the dynabase itself is not a ground
 * variable.  This would mean that we might attempt to save time by not
 * performing any rewrites against some group of expression until we have more information
 */
class DeferRewriteTillGround extends RuntimeException {

    public final RexprValueVariable variable;

    DeferRewriteTillGround(RexprValueVariable v) {
        super();
        variable = v;
    }

    @Override
    public Throwable fillInStackTrace() {
        if(is_debugging) {
            return super.fillInStackTrace();
        } else {
            return null;
        }
    }

    static final private boolean is_debugging = "true".equals(System.getProperty("dyna.debug", "true"));

}
