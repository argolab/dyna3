package dyna;

import java.util.*;
import clojure.lang.*;

// todo make this a full class..
public abstract class ClojureUnorderedVector extends AFn implements IPersistentVector, Iterable,
                                                           List,
                                                           RandomAccess, //Comparable,
                                                           //Serializable,
                                                           IHashEq
                                                           //IReduce, IKVReduce
{

    private int _hash = 0; // there is hash and
    public final Object[] vals;

    public ClojureUnorderedVector(Object[] vals, int _hash) {
        this.vals = vals;
        this._hash = _hash;
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
            h ^= vals[i].hashCode();
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



    public Object getFrequencyMap() {
        // TODO: make this faster using transient maps instead of something
        // which will have to get replaced each time
        Object m = RT.map();
        for(int i = 0; i < vals.length; i++) {
            int c = (Integer)RT.get(m, vals[i], 0);
            m = RT.assoc(m, vals[i], c+1);
        }
        return m;
    }


    static class VecTransientCollection implements ITransientCollection {
        static class Node {
            final Object val;
            final Node next;
            Node(Object v, Node n) { val = v; next = n; }
        }
        private Node head = null;
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
            assert(false);
            return null;
            //return new ClojureUnorderedVector
        }
    }

}
