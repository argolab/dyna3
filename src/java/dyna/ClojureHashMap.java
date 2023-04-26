package dyna;

import java.util.*;
import clojure.lang.*;
import clojure.lang.MapEntry;
import java.lang.ref.WeakReference;
import java.util.concurrent.Callable;


public final class ClojureHashMap extends AFn implements IPersistentMap,
                                                         IHashEq,
                                                         IEditableCollection,
                                                         IObj,
                                                         Map {

    private final INode root;
    private static final INode EMPTY_INODE = new EmptyNode();
    public static final ClojureHashMap EMPTY = new ClojureHashMap(EMPTY_INODE);
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
            for(Iterator<MapEntry> it = iterator(); it.hasNext();) {
                MapEntry e = it.next();
                Object r = m.get(e.getKey());
                if(r == null || !e.getValue().equals(r))
                    return false;
            }
            return true;
        }
    }

    public int hashCode() {
        assert(false); // TODO
        return 0;
    }
    public int hasheq() { return hashCode(); }

    public ITransientMap asTransient() {
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
        Object e = root.get_value(key, hash(key), 0, null);
        if(e != null) {
            return MapEntry.create(key, e);
        }
        return null;
    }

    public boolean equiv(Object o) {
        return equals(o);
    }

    public ClojureHashMap empty() { return EMPTY; }

    public IPersistentMap cons(Object o) {
        if(o instanceof Map.Entry) {
            Map.Entry m = (Map.Entry)o;
            return assoc(m.getKey(), m.getValue());
        } else if(o instanceof IPersistentVector) {
            if(RT.count(o) != 2)
                throw new IllegalArgumentException("Vector arg to map conj must be a pair");
            return assoc(RT.nth(o, 0), RT.nth(o, 1));
        } else {
            ITransientMap h = asTransient();
            for(ISeq s = RT.seq(o); s != null; s = s.next()) {
                Map.Entry e = (Map.Entry)s.first();
                h = h.assoc(e.getKey(), e.getValue());
            }
            return h.persistent();
        }
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
        return root.get_value(k, hash(k), 0, notfound);
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

    public Iterator<MapEntry> iterator() {
        try {
            return new IteratorImpl(root.get_node_iterator().call());
        } catch(Exception e) {
            throw new RuntimeException(e);
        }
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

    // these are unsupported because this is an immutable map
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

        public TransientHashMap assoc(Object key, Object val) {
            root = root.insert_or_update(this, key, val, ClojureHashMap.hash(key), 0);
            return this;
        }
        public TransientHashMap without(Object key) {
            root = root.insert_or_update(this, key, null, ClojureHashMap.hash(key), 0);
            return this;
        }
        public int count() {
            return root.size();
        }
        public Object valAt(Object key) { return valAt(key, null); }
        public Object valAt(Object key, Object notfound) {
            return root.get_value(key, ClojureHashMap.hash(key), 0, notfound);
        }
        public boolean containsKey(Object key) {
            return root.contains_key(key, ClojureHashMap.hash(key), 0);
        }
        public MapEntry entryAt(Object key) {
            Object e = root.get_value(key, hash(key), 0, null);
            if(e != null) {
                return MapEntry.create(key, e);
            }
            return null;
        }
        public TransientHashMap conj(Object o) {
            if(o instanceof Map.Entry) {
                Map.Entry m = (Map.Entry)o;
                return assoc(m.getKey(), m.getValue());
            } else if(o instanceof IPersistentVector) {
                if(RT.count(o) != 2)
                    throw new IllegalArgumentException("Vector arg to map conj must be a pair");
                return assoc(RT.nth(o, 0), RT.nth(o, 1));
            } else {
                for(ISeq s = RT.seq(o); s != null; s = s.next()) {
                    Map.Entry e = (Map.Entry)s.first();
                    assoc(e.getKey(), e.getValue());
                }
                return this;
            }
        }
    }



    static private abstract class INodeIterator {
        abstract boolean hasNext();
        abstract MapEntry next();

        Callable<INodeIterator> next_iterator = null;
        INodeIterator nextIterator() {
            try {
                if(next_iterator != null) {
                    INodeIterator r = next_iterator.call();
                    next_iterator = null;
                    return r;
                } else {
                    return null;
                }
            } catch(Exception e) {
                throw new RuntimeException(e);
            }
        }
        void setNextIterator(Callable<INodeIterator> c) {
            if(next_iterator == null) {
                next_iterator = c;
            } else {
                Callable<INodeIterator> cur = next_iterator;
                next_iterator = new Callable<INodeIterator>() {
                        public INodeIterator call() throws Exception {
                            INodeIterator r = cur.call();
                            r.setNextIterator(c);
                            return r;
                        }
                    };
            }
        }
        void setNextIterator(INodeIterator i) {
            setNextIterator(new Callable<INodeIterator>() {
                    public INodeIterator call() {
                        return i;
                    }
                });
        }
    }

    static private abstract class INode {

        int key_hash = 0;

        public abstract INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset);// { return null; }

        public abstract boolean contains_key(Object key, int hash, int hashOffset);// { return false; }

        public abstract Object get_value(Object key, int hash, int hashOffset, Object not_found);// { return null; }

        public abstract int size();// { return 0; }

        public abstract Callable<INodeIterator> get_node_iterator();

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
            if(o == this) return true;
            if(!(o instanceof LeafSingleNode)) return false;
            LeafSingleNode s = (LeafSingleNode)o;
            return key.equals(s.key) && value.equals(s.value);
        }

        public int size() { return 1; }

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

        public boolean contains_key(Object key, int hash, int hashOffset) {
            return this.key.equals(key);
        }

        public Object get_value(Object key, int hash, int hashOffset, Object not_found) {
            if(this.key.equals(key))
                return value;
            return not_found;
        }

        public Callable<INodeIterator> get_node_iterator() {
            return new Callable<INodeIterator>() {
                public INodeIterator call() {
                    return new INodeIterator() {
                        boolean consumed = false;
                        public MapEntry next() {
                            if(!consumed) {
                                consumed = true;
                                return MapEntry.create(key, value);
                            }
                            return null;
                        }
                        public boolean hasNext() { return !consumed; }
                    };
                }
            };
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

        public static INode create(Object modifier, Object[] ks, Object[] vs, int hashOffset) {
            if(ks.length == 1) {
                return LeafSingleNode.create(ks[0], vs[0]);
            }
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
        public boolean equals(Object o) {
            if(o == this) return true;
            if(!(o instanceof LeafMultipleNode)) return false;
            LeafMultipleNode m = (LeafMultipleNode)o;
            if(m.keys.length != keys.length) return false;
            for(int i = 0; i < keys.length; i++) {
                boolean found = false;
                for(int j = 0; j < m.keys.length; j++) {
                    if(keys[i].equals(m.keys[j])) {
                        found = true;
                        if(!values[i].equals(m.values[j])) return false;
                        break;
                    }
                }
                if(!found) return false;
            }
            return true;
        }

        public int size() {
            return keys.length;
        }

        public boolean contains_key(Object key, int hash, int hashOffset) {
            for(int i = 0; i < keys.length; i++)
                if(keys[i].equals(key))
                    return true;
            return false;
        }

        public Object get_value(Object key, int hash, int hashOffset, Object not_found) {
            for(int i = 0; i < keys.length; i++) {
                if(keys[i].equals(key))
                    return values[i];
            }
            return not_found;
        }

        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            boolean can_modify = this.can_modify != null && this.can_modify.get() == modifier;
            if(!can_modify) this.can_modify = null;
            int lhash = ClojureHashMap.hash(keys[0]);
            if(lhash == hash) {
                // then this is the same hash, so we have to add it to this collection
                Object[] new_keys = new Object[keys.length+1];
                Object[] new_values = new Object[values.length+1];
                System.arraycopy(keys, 0, new_keys, 0, keys.length);
                System.arraycopy(values, 0, new_values, 0, values.length);
                new_keys[new_keys.length-1] = key;
                new_values[new_values.length-1] = values;
                if(can_modify) {
                    keys = new_keys;
                    values = new_values;
                    _hash = 0;
                    return this;
                } else {
                    return new LeafMultipleNode(modifier, new_keys, new_values);
                }
            } else {
                return InternalNode.create(modifier, new INode[]{this,LeafSingleNode.create(key, value)}, new int[]{lhash, hash}, hashOffset);
            }
        }

        public Callable<INodeIterator> get_node_iterator() {
            return new Callable<INodeIterator>() {
                public INodeIterator call() {
                    return new INodeIterator() {
                        int index = 0;
                        public MapEntry next() {
                            if(index < keys.length) {
                                MapEntry r = MapEntry.create(keys[index], values[index]);
                                index++;
                                return r;
                            }
                            return null;
                        }
                        public boolean hasNext() {
                            return index < keys.length;
                        }
                    };
                }
            };
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

        public static InternalNode create(Object modifier, INode[] nodes, int[] key_hashes, int hashOffset) {
            return new InternalNode(modifier, nodes, key_hashes, hashOffset);
        }

        private InternalNode(final Object modifier, final Object[] keys, final Object[] vals, final int hashOffset) {
            if(modifier != null) can_modify = new WeakReference<>(modifier);
            for(int i = 0; i < keys.length; i++) {
                int h = ClojureHashMap.hash(keys[i]);
                int d = (h >> hashOffset) & 7;
                INode n = children[d];
                if(n == null) n = ClojureHashMap.EMPTY_INODE;
                children[d] = n.insert_or_update(modifier, keys[i], vals[i], h, hashOffset+3);
            }
        }

        private InternalNode(Object modifier, INode[] nodes, int[] key_hashes, int hashOffset) {
            if(modifier != null) can_modify = new WeakReference<>(modifier);
            assert(nodes.length == key_hashes.length);
            for(int i = 0; i < nodes.length; i++) {
                int d = (key_hashes[i] >> hashOffset) & 7;
                assert(children[d] == null);
                children[d] = nodes[i];
            }
        }

        private InternalNode(Object modifier) {
            if(modifier != null) can_modify = new WeakReference<>(modifier);
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

        public boolean equals(Object o) {
            if(o == this) return true;
            if(!(o instanceof InternalNode)) return false;
            InternalNode m = (InternalNode)o;
            if(_hash != 0 && m._hash != 0 && _hash != m._hash) return false;
            if(_size != 0 && m._size != 0 && _size != m._size) return false;
            for(int i = 0; i < children.length; i++) {
                if(children[i] == null) { if(m.children[i] != null) return false; }
                else if(!children[i].equals(m.children[i])) return false;
            }
            return true;
        }

        public boolean contains_key(Object key, int hash, int hashOffset) {
            int idx = hash >> hashOffset;
            INode c = children[idx & 7];
            return c != null && c.contains_key(key, hash, hashOffset+3);
        }

        public Object get_value(Object key, int hash, int hashOffset, Object not_found) {
            int idx = hash >> hashOffset;
            INode c = children[idx & 7];
            if(c != null) return c.get_value(key, hash, hashOffset+3, not_found);
            return not_found;
        }

        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            boolean can_modify = this.can_modify != null && this.can_modify.get() == modifier;
            if(!can_modify) this.can_modify = null;
            int d = (hash >> hashOffset) & 7;
            if(can_modify) {
                INode n = children[d];
                if(n == null) n = ClojureHashMap.EMPTY_INODE;
                children[d] = n.insert_or_update(modifier, key, value, hash, hashOffset+3);
                _hash = _size = 0;
                return this;
            } else {
                InternalNode ret = new InternalNode(modifier);
                System.arraycopy(children, 0, ret.children, 0, 8);
                INode n = children[d];
                if(n == null) n = ClojureHashMap.EMPTY_INODE;
                ret.children[d] = n.insert_or_update(modifier, key, value, hash, hashOffset+3);
                return ret;
            }
        }

        public Callable<INodeIterator> get_node_iterator() {
            return new Callable<INodeIterator>() {
                public INodeIterator call() throws Exception {
                    INodeIterator ret = null;
                    for(int i = 0; i < children.length; i++) {
                        if(children[i] != null) {
                            if(ret == null) ret = children[i].get_node_iterator().call();
                            else ret.setNextIterator(children[i].get_node_iterator());
                        }
                    }
                    return ret;
                }
            };
        }

    }

    static private class EmptyNode extends INode {
        public int size() { return 0; }
        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            return LeafSingleNode.create(key,value);
        }
        public boolean contains_key(Object key, int hash, int hashOffset) { return false; }
        public Object get_value(Object key, int hash, int hashOffset, Object not_found) { return not_found; }
        public Callable<INodeIterator> get_node_iterator() {
            return new Callable<INodeIterator>() {
                public INodeIterator call() {
                    return new INodeIterator() {
                        public boolean hasNext() { return false; }
                        public MapEntry next() { return null; }
                    };
                }
            };
        }
    }

    static private class IteratorImpl implements Iterator<MapEntry> {

        INodeIterator current;

        IteratorImpl(INodeIterator i) {
            current = i;
            hasNext();
        }

        public MapEntry next() {
            if(current != null) {
                MapEntry r = current.next();
                hasNext(); // make sure that if the iterator is done, that it moves to the next one
                return r;
            }
            return null;
        }

        public boolean hasNext() {
            while(current != null && !current.hasNext())
                current = current.nextIterator();
            return current != null;
        }

    }

}
