package dyna;

/**
 * A function can be called from dyna as long as it implements this interface and is passed to DynaInterface/define_external_function
 */
interface ExternalFunction {
    Object call(Object... args);
}
