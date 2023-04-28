package dyna;

import clojure.lang.RT;

/**
 * A wrapper around a hash map
 */
final public class DynaMap {
    final public Object map_elements;

    public DynaMap(Object m) {
        map_elements = m;
    }

    public static DynaMap create(Object[] args) {
        return new DynaMap(RT.map(args));
    }

}
