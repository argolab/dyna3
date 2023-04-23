package dyna;

import java.util.*;
import clojure.lang.*;
import java.lang.ref.WeakReference;


public final class ClojureHashMap extends AFn implements IPersistentMap,
                                                         IHashEq,
                                                         IEditableCollection,
                                                         IObj,
                                                         Map {

    private final INode root;
    private static final INode EMPTY_INODE = new EmptyNode();
    private static final ClojureHashMap EMPTY = new ClojureHashMap(EMPTY_INODE);
    private static final Object NOT_FOUND = new Object();

    ClojureHashMap(INode r) {
        root = r;
        assert(root != null);
    }

    public boolean equals(Object o) {
        if(o instanceof ClojureHashMap) {
            return root.equals(((ClojureHashMap)o).root);
        } else {
            if(!(o instanceof Map)) return false;
            Map m = (Map)o;
            if(m.size() != count()) return false;

        }
        return false;
    }

    public int hashCode() { return 0; }
    public int hasheq() { return hashCode(); }

    public ITransientMap asTransient() {
        // this could just use a java hashmap and then build up from there?
        return new TransientHashMap(root);
    }

    public ClojureHashMap assoc(Object key, Object val) {
        return new ClojureHashMap(root.insert_or_update(null, key, val, hash(key), 0));
    }

    public ClojureHashMap assocEx(Object key, Object val) {
        if(containsKey(key))
            throw Util.runtimeException("Key already present");
        return assoc(key, val);
    }

    public ClojureHashMap without(Object key) {
        return new ClojureHashMap(root.insert_or_update(null, key, null, hash(key), 0));
    }

    public boolean containsKey(Object key) {
        return root.contains_key(key, hash(key), 0);
    }

    public MapEntry entryAt(Object key) {
        return null;
    }

    public boolean equiv(Object o) {
        return equals(o);
    }

    public ClojureHashMap empty() { return EMPTY; }

    public ClojureHashMap cons(Object arg) {
        return assoc(RT.first(arg), RT.second(arg));
    }

    public int count() {
        return root.size();
    }

    public ISeq seq() {
        return RT.seq(iterator());
    }

    public Object valAt(Object k) {
        return valAt(k, null);
    }

    public Object valAt(Object k, Object notfound) {
        return null;
    }

    public IObj withMeta(IPersistentMap meta) {
        if(meta == null || meta.count() == 0)
            return this;
        throw new UnsupportedOperationException();
    }

    public IPersistentMap meta() {
        return null;
    }



    private static int hash(Object key, Object value) {
        return key.hashCode() ^ value.hashCode();  // this should do a lot more to shuffle stuff around
    }

    private static int hash(Object k) {
        return k == null ? 0 : k.hashCode(); // this could use the hasheq from clojure which might be a bit better???
    }

    private static boolean equals(Object a, Object b) {
        return a == null ? b == null : a.equals(b);
    }

    static private final class MapEntry implements IMapEntry {
        public Object key() { return null; }
        public Object val() { return null; }

        public boolean equals(Object o) { return false; }

        public int hashCode() { return 0; }

        public Object getKey() { return key(); }
        public Object getValue() { return val(); }
        public Object setValue(Object n) {
            throw new UnsupportedOperationException();
        }
    }

    public Iterator<MapEntry> iterator() {
        return new INodeIterator(root);
    }

    public Set<MapEntry> entrySet() {
        throw new UnsupportedOperationException();
    }

    public Set keySet() {
        throw new UnsupportedOperationException();
    }

    public Collection<Object> values() {
        throw new UnsupportedOperationException();
    }

    public void clear() { throw new UnsupportedOperationException(); }

    public void putAll(Map x) {
        throw new UnsupportedOperationException();
    }

    public Object remove(Object k) {
        throw new UnsupportedOperationException();
    }

    public Object put(Object k, Object v) {
        throw new UnsupportedOperationException();
    }

    public Object get(Object k) { return valAt(k); }

    public boolean containsValue(Object v) {
        // this could be supported by just iterating through everything....
        throw new UnsupportedOperationException();
    }

    public boolean isEmpty() { return count() == 0; }

    public int size() { return count(); }

    static private class TransientHashMap implements ITransientMap,ITransientAssociative2 {
        private INode root;

        TransientHashMap(INode root) {
            this.root = root;
        }

        public ClojureHashMap persistent() {
            ClojureHashMap r = new ClojureHashMap(root);
            this.root = null;
            return r;
        }

        public TransientHashMap assoc(Object key, Object val) { return this; }
        public TransientHashMap without(Object key) { return this; }
        public int count() { return 0; }
        public Object valAt(Object key) { return valAt(key, null); }
        public Object valAt(Object key, Object notfound) {
            return null;
        }
        public boolean containsKey(Object key) {
            return false;
        }
        public MapEntry entryAt(Object key) {
            return null;
        }
        public TransientHashMap conj(Object x) {
            return this;
        }
    }

    static private abstract class INode {

        int key_hash = 0;

        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) { return null; }

        public boolean contains_key(Object key, int hash, int hashOffset) { return false; }

        // public INode remove(Object modifier, Object key, int hash, int hashOffset) { return null; }

        public int size() { return 0; }

    }

    static private class LeafSingleNode extends INode {
        final Object key;
        final Object value;

        private LeafSingleNode(Object k, Object v) {
            this.key = k;
            this.value = v;
            key_hash = ClojureHashMap.hash(k);
        }

        public static LeafSingleNode create(Object k, Object v) {
            if(v == null) return null;
            return new LeafSingleNode(k, v);
        }

        public int hashCode() {
            return ClojureHashMap.hash(key, value);
        }

        public boolean equals(Object o) {
            if(!(o instanceof LeafSingleNode)) return false;
            LeafSingleNode s = (LeafSingleNode)o;
            return key.equals(s.key) && value.equals(s.value);
        }

        public int size() { return 1; }

        // public INode remove(Object modifier, Object key, int hash, int hashOffset) {
        //     if(ClojureHashMap.equals(this.key, key)) return null;
        //     return this;
        // }

        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            if(hash == key_hash) {
                if(ClojureHashMap.equals(this.key, key))
                    return LeafSingleNode.create(key, value);
                else
                    return LeafMultipleNode.create(modifier, new Object[]{this.key,key}, new Object[]{this.value,value}, hashOffset);
            } else {
                return InternalNode.create(modifier, new Object[]{this.key,key}, new Object[]{this.value,value}, hashOffset);
            }
        }
    }

    static private class LeafMultipleNode extends INode {
        Object[] keys;
        Object[] values;
        WeakReference<Object> can_modify = null;
        int _hash = 0;

        private LeafMultipleNode(Object modifier, Object[] ks, Object[] vs) {
            // all of the key hashes should be the same then
            key_hash = ClojureHashMap.hash(ks[0]);
            assert(ks.length > 1);
            for(int i = 0; i < ks.length; i++) assert(ClojureHashMap.hash(ks[1]) == key_hash);
            keys = ks;
            values = vs;
            if(modifier != null) can_modify = new WeakReference<Object>(modifier);
        }

        public static LeafMultipleNode create(Object modifier, Object[] ks, Object[] vs, int hashOffset) {
            return new LeafMultipleNode(modifier, ks, vs);
        }

        public int hashCode() {
            if(_hash != 0) return _hash;
            int h = 0;
            for(int i = 0; i < keys.length; i++) {
                h ^= ClojureHashMap.hash(keys[i], values[i]);
            }
            _hash = h;
            return h;
        }
        public int size() {
            return keys.length;
        }
    }

    static private class InternalNode extends INode {
        final INode children[] = new INode[8];
        WeakReference<Object> can_modify = null;
        int _hash = 0;
        int _size = 0;

        public static InternalNode create(Object modifier, Object[] ks, Object[] vs, int hashOffset) {
            return new InternalNode(modifier, ks, vs, hashOffset);
        }

        InternalNode(final Object modifier, final Object[] keys, final Object[] vals, final int hashOffset) {
            if(modifier != null) can_modify = new WeakReference<>(modifier);
            for(int i = 0; i < keys.length; i++) {
                int h = ClojureHashMap.hash(keys[i]);
                int d = (h >> hashOffset) & 7;
                INode n = children[d];
                if(n == null) n = ClojureHashMap.EMPTY_INODE;
                children[d] = n.insert_or_update(modifier, keys[i], vals[i], h, hashOffset+3);
            }
        }

        public int size() {
            if(_size != 0) return _size;
            int s = 0;
            for(int i = 0; i < children.length; i++)
                if(children[i] != null)
                    s += children[i].size();
            _size = s;
            return s;
        }
    }

    static private class EmptyNode extends INode {
        public int size() { return 0; }
        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            return LeafSingleNode.create(key,value);
        }
    }

    static private class INodeIterator implements Iterator<MapEntry> {

        INodeIterator(INode r) {}

        public MapEntry next() {
            return null;
        }

        public boolean hasNext() {
            return false;
        }

    }

}
