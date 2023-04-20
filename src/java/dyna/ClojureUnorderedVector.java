package dyna;

import java.util.*;
import clojure.lang.*;

// todo make this a full class..
public class ClojureUnorderedVector extends AFn implements IPersistentVector,
                                                           //Iterable,
                                                           RandomAccess, //Comparable,
                                                           //Serializable,
                                                           IHashEq,
                                                           //IReduce, IKVReduce
                                                           IEditableCollection,
                                                           IObj
{

    private int _hash = 0; // there is hash and
    public final Object[] vals;

    public static final ClojureUnorderedVector EMPTY = new ClojureUnorderedVector(new Object[]{}, 0);

    private ClojureUnorderedVector(Object[] vals, int _hash) {
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

    public boolean equals(Object other) {
        if(!(other instanceof ClojureUnorderedVector)) return false;
        ClojureUnorderedVector o = (ClojureUnorderedVector)other;
        if(count() != o.count()) return false;
        if(hashCode() != o.hashCode()) return false;
        if(count() == 1) {
            return Util.equiv(vals[0], o.vals[0]);
        }
        return getFrequencyMap().equals(o.getFrequencyMap());
        // because of the unordered nature, we are going to have to count the
        // number of times that each of these elements appears in the map
        //
        // which means using something like a hashMap
    }

    public int hashCode() {
        if(_hash != 0)
            return _hash;
        int h = 0xdeadbeef;
        for(int i = 0; i < vals.length; i++) {
            h ^= hash(vals[i]);
        }
        h += vals.length;
        _hash = h;
        return h;
    }

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
        int h = 0;
        if(_hash != 0) { h = ((_hash - vals.length) ^ hash(val)) + a.length; }
        return new ClojureUnorderedVector(a, h);
    }

    public ClojureUnorderedVector assocN(int i, Object val) {
        int l = vals.length > i ? vals.length : i+1;
        Object a[] = new Object[vals.length];
        System.arraycopy(vals,0,a,0,vals.length);
        a[i] = val;
        int h = _hash;
        if(h != 0) { h = ((h - vals.length) ^ hash(vals[i]) ^ hash(a[i])) + vals.length; }
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
        return RT.seq(vals);
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
        if(h != 0) { h = ((h - vals.length) ^ hash(vals[0])) + a.length; }
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

    static private int hash(Object h) {
        return h == null ? 0 : h.hashCode();
    }

}
