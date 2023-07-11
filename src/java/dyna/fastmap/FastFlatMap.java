package dyna.fastmap;

import sun.misc.Unsafe;

import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * A hash map which will generate custom classes to quickly
 */
public class FastFlatMap {
    private FastFlatMap() {
    }


    static abstract class MapInternal {
        public abstract MapInternal set(Object key, Object val);

        public abstract Object get(Object key);

        public abstract int num_entries();

        public abstract Object get_key(int i);  // these could use unsafe internally which would allow it to treat the object like an array

        public abstract Object get_value(int i);
    }

    static abstract class MapExtendNewElement {
        public abstract MapInternal set_new(MapInternal existing_map, Object key, Object value);
    }

    /**
     * Thrown when the reference pointer needs to be updated for which donwstream classes are going to be generated as a result
     */
    static final class MapExtendNewChangeRef extends RuntimeException {
        @Override
        public Throwable fillInStackTrace() { return null; }
        public final MapExtendNewElement new_ref;
        public final MapInternal map_result;

        public MapExtendNewChangeRef(MapExtendNewElement a, MapInternal b) {
            new_ref = a;
            map_result = b;
        }
    }

    public static final class Map {
        private MapInternal m;
        Map(MapInternal x) { m = x; }
        public void set(Object key, Object val) {
            m = m.set(key, val); // this might return a new internal map, or it might return the same value
        }
        public Object get(Object key) {
            return m.get(key);
        }
        public int size() {
            final MapInternal l = m;
            int r = 0;
            final int ents = l.num_entries();
            for(int i = 0; i < ents; i++)
                if(l.get_value(i) != null)
                    r++;
            return r;
        }

        public boolean empty() {
            final MapInternal l = m;
            final int ent = l.num_entries();
            for(int i = 0; i < ent; i++)
                if(l.get_value(i) != null)
                    return false;
            return true;
        }
    }

    private static boolean can_use_pointer_equality(Object key) {
        // look at the class of this and return true if we can use pointer equality without having to call .equals
        // this will make it faster
        return false;
    }


    static private final Object static_key_lock = new Object();
    static private final HashMap<Long, Object> static_keys = new HashMap<>();
    static private final AtomicLong static_key_counter = new AtomicLong();

    static Object _get_static_key(long k) {
        synchronized(static_key_lock) {
            Object r = static_keys.get(k);
            static_keys.remove(k);
            return r;
        }
    }

    final static sun.misc.Unsafe theUnsafe;

    static {
        sun.misc.Unsafe v = null;
        try {
            Field f = sun.misc.Unsafe.class.getDeclaredField("theUnsafe");
            f.setAccessible(true);
            v = (sun.misc.Unsafe) f.get(null);
        }
        catch (NoSuchFieldException e) {}
        catch (IllegalArgumentException e) {}
        catch (IllegalAccessException e) {}
        theUnsafe = v;
    }


}
