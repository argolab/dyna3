package dyna;

import java.util.*;
import clojure.lang.*;

/**
 * This is an alternate implementation of the vector class used by the
 * prefix_trie.clj class for its internal implementation.  This class is a bit
 * simpler than clojures' vector class as it is only backed by a single internal
 * array.  Therefore when doing operations such as cons using this class, it
 * will be less efficient.  In our case, we expect that the internal arrays held
 * by this class will likely be small (a few elements at a time).  And mostly
 * rewritten all at the same time (hence, it does not make much sense to
 * optimize for insert operations).
 *
 * This class is "unordered" (like a bag), so [1 2 3 4] equals [4 1 3 2].  Also,
 * this class will update the hash code instead of recomputing it from scratch
 * when there are changes.
 */
public final class ClojureUnorderedVector extends AFn implements IPersistentVector,
                                                           //Iterable,
                                                           RandomAccess, //Comparable,
                                                           //Serializable,
                                                           IHashEq,
                                                           //IReduce, IKVReduce
                                                           IEditableCollection,
                                                           IObj
{

    private int _hash = 0;  // a cache for the hash of the objects
    public final Object[] vals;

    public static final ClojureUnorderedVector EMPTY = new ClojureUnorderedVector(new Object[]{}, 0);

    private ClojureUnorderedVector(Object[] vals, int _hash) {
        assert(vals != null);
        this.vals = vals;
        this._hash = _hash;
    }

    public ClojureUnorderedVector(Object v) {
        if(v instanceof ClojureUnorderedVector) {
            ClojureUnorderedVector o = (ClojureUnorderedVector)v;
            _hash = o._hash;
            vals = new Object[o.vals.length];
            System.arraycopy(o.vals,0,vals,0,o.vals.length);
        } else {
            int length = RT.count(v);
            vals = new Object[length];
            for(int i = 0; i < length; i++) {
                vals[i] = RT.nth(v, i);
            }
        }
    }

    public static ClojureUnorderedVector create(Object args) {
        if(args instanceof ClojureUnorderedVector)
            return (ClojureUnorderedVector)args;
        return new ClojureUnorderedVector(args);
    }

    public boolean equals(Object other) {
        if(this == other) return true;
        if(other instanceof ClojureUnorderedVector) {
            ClojureUnorderedVector o = (ClojureUnorderedVector)other;
            if(count() != o.count()) return false;
            if(hashCode() != o.hashCode()) return false;
            if(count() == 1) {
                return Util.equiv(vals[0], o.vals[0]);
            }
            // because of the unordered nature, we are going to have to count the
            // number of times that each of these elements appears in the map
            //
            // which means using something like a hashMap
            return getFrequencyMap().equals(o.getFrequencyMap());
        } else {
            if(count() != RT.count(other)) return false;
            Object s = RT.seq(other);
            ITransientMap m = PersistentHashMap.EMPTY.asTransient();
            while(s != null) {
                Object v = RT.first(s);
                int c = (Integer)RT.get(m, v, 0);
                m = m.assoc(v, c+1);
                s = RT.next(s);
            }
            return getFrequencyMap().equals(m.persistent());
        }
    }

    public int hashCode() {
        // eh, probably not a great hash, but should be decent enough (hopefully)
        int h = hashInternal() + vals.length;
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 13;
        int l = hashLengthCodes[(vals.length * (h >> 10)) & 127];
        l = Integer.rotateLeft(l, (h^(h>>20))&15);
        h ^= l;
        h ^= h >> 5;
        h *= 0xc2b2ae35;
        h ^= h >> 16;
        return  h;
    }

    private int hashInternal() {
        if(_hash != 0) return _hash;
        int h = 0;
        for(int i = 0; i < vals.length; i++) {
            h ^= hash(vals[i]);
        }
        _hash = h;
        return h;
    }

    private static final int hashLengthCodes[] = new int[] { // 128 different numbers which will get shuffled into the code
        597164378,  976600812,   62924696, 1630519828, 1269576953,
        1073851686,  313560563,  914450662, 1473291817,   29561511,
        2058145373, 1055075321, 1690157812,  903822113, 1711424116,
        727951103,  686515870,  708104307, 2134809801,  623376737,
        2046717049, 1167862095,  816242418,  954757334,  819860582,
        1377590620, 2032725095, 1768598511, 1464040856, 1650972854,
        1697456990,  243304649, 1303505355,  953897630,  354398211,
        1963840659, 1048406214, 1011986554,  591020305, 1777792790,
        214851141,  927388513, 1471254200, 1771940495,  660345542,
        1076967111,  180699013, 1541684179, 2080757920,  979887472,
        910719318, 1864325250,  982383862,  698723590, 1602608609,
        1577236254,  738887741,  660786560, 1108795353, 2002397925,
        148637919,  229614181,  489861505, 1729342076, 1207730783,
        1625211364, 1270628662,   27326889,  796351079,  906056506,
        1135126304,  603811104, 2116072586, 1299169065, 1594168154,
        1238571850,   61405081, 1477599035,  446113839, 1206295293,
        2059672457,  915463885, 1803259340,  564245662, 1218359760,
        1660705314, 1351421505,  237817429, 1113006610, 1317108602,
        47327975, 1114125848, 2051097259,  605677971, 1876005703,
        1679153843, 1335619269, 1095148213, 1942757823,  312468049,
        425205755,  202289932,  320151538, 1970421861, 1145384240,
        905797029, 2002060918, 1190983952,  548320185, 1555063757,
        1629691965, 1710279957, 1504309567, 1300128911,  397467516,
        98494146, 1227657446,  106779726,   73565497,  917457706,
        166548552, 1823913412,  118375438, 1113388665,  680749667,
        576500507, 1159445553, 1463481156 };

    public int hasheq() { return hashCode(); }

    public Object nth(int i, Object notfound) {
        if(i >= 0 && i < vals.length) return vals[i];
        return notfound;
    }

    public int count() { return vals.length; }

    public IPersistentMap getFrequencyMap() {
        // TODO: make this faster using transient maps instead of something
        // which will have to get replaced each time
        //Object m = RT.map();
        //ITransientMap m = RT.map().asTransient();
        ITransientMap m = PersistentHashMap.EMPTY.asTransient();
        for(int i = 0; i < vals.length; i++) {
            int c = (Integer)RT.get(m, vals[i], 0);
            m = m.assoc(vals[i], c+1);//RT.assoc(m, vals[i], c+1);
        }
        return m.persistent();
    }

    public ClojureUnorderedVector cons(Object val) {
        Object a[] = new Object[vals.length+1];
        System.arraycopy(vals,0,a,0,vals.length);
        a[a.length-1] = val;
        int h = _hash;
        if(h != 0) { h ^= hash(vals); }
        return new ClojureUnorderedVector(a, h);
    }

    public ClojureUnorderedVector assocN(int i, Object val) {
        int l = vals.length > i ? vals.length : i+1;
        Object a[] = new Object[vals.length];
        System.arraycopy(vals,0,a,0,vals.length);
        a[i] = val;
        int h = _hash;
        if(h != 0) { h ^= hash(vals[i]) ^ hash(a[i]); }
        return new ClojureUnorderedVector(a, h);
    }

    public int length() { return count(); }

    public ClojureUnorderedVector assoc(Object key, Object val) {
        return assocN(((Number)key).intValue(), val);
    }

    public IMapEntry entryAt(Object key) {
        if(Util.isInteger(key)) {
            return new MapEntry(this, ((Number)key).intValue());
        }
        return null;
    }

    public boolean containsKey(Object key) {
        if(Util.isInteger(key)) {
            int i = ((Number)key).intValue();
            return i >= 0 && i < vals.length;
        }
        return false;
    }

    public boolean equiv(Object o) {
        return equals(o);
    }

    public ClojureUnorderedVector empty() { return EMPTY; }

    public ISeq seq() {
        return ArraySeq.create(vals);
        //return RT.seq(vals);
    }

    public Object valAt(Object key) {
        return valAt(key,null);
    }

    public Object valAt(Object key, Object notfound) {
        return Util.isInteger(key) ? nth(((Number)key).intValue(), notfound) : notfound;
    }

    public Object peek() {
        return vals.length > 0 ? vals[0] : null;
    }

    public ClojureUnorderedVector pop() {
        if(vals.length <= 1) return EMPTY;
        Object a[] = new Object[vals.length-1];
        System.arraycopy(vals,1,a,0,vals.length-1);
        int h = _hash;
        if(h != 0) { h ^= hash(vals[0]); }
        return new ClojureUnorderedVector(a, h);
    }

    public ISeq rseq() {
        throw new UnsupportedOperationException();
    }

    public Object nth(int i) {
        return nth(i, null);
    }


    public ITransientCollection asTransient() {
        VecTransientCollection c = new VecTransientCollection();
        for(int i = vals.length-1; i >= 0; i--) {
            c = c.conj(vals[i]);
        }
        return c;
    }

    public IObj withMeta(IPersistentMap meta) {
        if(meta == null || meta.count() == 0)
            return this;
        throw new UnsupportedOperationException();
    }

    public IPersistentMap meta() {
        return null;
    }

    public Object invoke(Object arg) {
        return valAt(arg);
    }

    public Object invoke(Object arg1, Object arg2) {
        return valAt(arg1, arg2);
    }

    static class VecTransientCollection implements ITransientCollection {
        static class Node {
            final Object val;
            final Node next;
            Node(Object v, Node n) { val = v; next = n; }
        }
        private Node head = null;
        VecTransientCollection() {}
        public VecTransientCollection conj(Object val) {
            head = new Node(val, head);
            return this;
        }

        public ClojureUnorderedVector persistent() {
            int length = 0;
            for(Node n = head; n != null; length++) n = n.next;
            Object[] arr = new Object[length];
            for(Node n = head; n != null;) {
                arr[--length] = n.val;
                n = n.next;
            }
            return new ClojureUnorderedVector(arr, 0);
        }
    }

    private static class MapEntry implements IMapEntry {
        private final int indx;
        private final ClojureUnorderedVector owner;
        MapEntry(ClojureUnorderedVector o, int i) {
            owner = o;
            indx = i;
        }

        public Object key() { return indx; }
        public Object val() { return owner.vals[indx]; }

        public boolean equals(Object o) {
            if(!(o instanceof MapEntry)) return false;
            MapEntry m = (MapEntry)o;
            return m.indx == indx && m.owner == owner;
        }

        public int hashCode() {
            return owner.hashCode() * 53 + indx;
        }

        public Object getKey() { return key(); }
        public Object getValue() { return val(); }
        public Object setValue(Object n) {
            throw new UnsupportedOperationException();
            // if this is a functional data structure, then we are not going to allow for its internal values to get changed
            // Object old = owner.vals[indx];
            // owner.vals[indx] = n;
            // return old;
        }

    }

    static private int hash(Object o) {
        if(o == null) return 0;
        int h = o.hashCode();
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 12;
        return h;
    }

    static public ClojureUnorderedVector concat(Object args_list) {
        int length = 0;
        final Object seq = RT.seq(args_list);
        Object n = seq;
        while(n != null) {
            length += RT.count(RT.first(n));
            n = RT.next(n);
        }
        Object[] arr = new Object[length];
        n = seq;
        int i = 0;
        while(n != null) {
            Object v = RT.first(n);
            if(v instanceof ClojureUnorderedVector) {
                ClojureUnorderedVector c = (ClojureUnorderedVector)v;
                System.arraycopy(c.vals,0, arr,i, c.vals.length);
                i += c.vals.length;
            } else {
                while(v != null) {
                    arr[i] = RT.first(v);
                    v = RT.next(v);
                    i++;
                }
            }
            n = RT.next(n);
        }
        return new ClojureUnorderedVector(arr, 0);
    }

}
