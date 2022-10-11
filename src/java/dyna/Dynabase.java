package dyna;

/**
 * Represent a handle for a dynabase
 */
final public class Dynabase {
    public final Object access_map;
    public Dynabase(Object m) {
        access_map = m;
    }
    public int hashCode() {
        return access_map == null ? 0 : access_map.hashCode();
    }
    public boolean equals(Object o) {
        return (o instanceof Dynabase) && (access_map == null ? ((Dynabase)o).access_map == null : access_map.equals(((Dynabase)o).access_map));
    }
    public String toString() {
        if(access_map != null) {
            return "(Dynabase " + access_map + ")";
        } else {
            return "(Dynabase null)";
        }
    }
}
