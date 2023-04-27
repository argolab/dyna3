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
                                                         Map,
                                                         MapEquivalence {

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
            ClojureHashMap c = (ClojureHashMap)o;
            return c.root == root || (c.root.size() == root.size() && c.root.hashCode() == root.hashCode() && root.equals(c.root, 0));
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
        int h = root.hashCode();
        int s = root.size();
        h = Integer.rotateLeft(h, 16 + s&15);
        h ^= (h ^ hashLengthCodes[h & 127]) * hashLengthCodes[s & 127];
        return h;
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
        return valAt(key, root) != root;
    }

    public MapEntry entryAt(Object key) {
        Object e = root.get_value(key, hash(key), 0, null);
        if(e != null) {
            return MapEntry.create(key, e);
        }
        return null;
    }

    public boolean equiv(Object o) {
        return (o instanceof MapEquivalence) && equals(o);
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
        return RT.chunkIteratorSeq(iterator());
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
        if(key == null || value == null) return 0;
        int k = hash(key), v = hash(value);
        for(int i = 0; i < 8; i++) {
            int g = hashPairCodes[(v >> (i*4) & 15) + i*16];
            k = Integer.rotateLeft(k, g & 15) * (1 + (g&255)) ^ (g >> 8);
        }
        return k;
    }

    private static int hash(Object k) {
        if(k == null) return 0;
        int h = (k instanceof IHashEq) ? ((IHashEq)k).hasheq() : k.hashCode();
        h ^= h >> 16;
        h *= 0x85ebca6b;
        h ^= h >> 13;
        h *= hashSingleItemCodes[h & 127];
        h ^= hashSingleItemCodes2[(h >> 12) & 127];
        return h;
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
            return valAt(key, root) != root;
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

        public abstract INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset);// { return null; }

        //public abstract boolean contains_key(Object key, int hash, int hashOffset);// { return false; }

        public abstract Object get_value(Object key, int hash, int hashOffset, Object not_found);// { return null; }

        public abstract int size();// { return 0; }

        public abstract Callable<INodeIterator> get_node_iterator();

        public abstract int hashCode();
        public abstract boolean equals(INode o, int hashOffset);
        public boolean equals(Object o) { throw new UnsupportedOperationException(); } // use the other equals method

    }

    static private class LeafSingleNode extends INode {
        final Object key;
        final Object value;
        final int key_hash;

        private LeafSingleNode(Object k, Object v, int hash) {
            this.key = k;
            this.value = v;
            key_hash = hash;
        }

        public static LeafSingleNode create(Object k, Object v, int hash) {
            if(v == null) return null;
            return new LeafSingleNode(k, v, hash);
        }

        public int hashCode() {
            return ClojureHashMap.hash(key, value);
        }

        public boolean equals(INode o, int hashOffset) {
            if(o == this) return true;
            if(!(o instanceof LeafSingleNode)) return false;
            LeafSingleNode s = (LeafSingleNode)o;
            return ClojureHashMap.equals(key, s.key) && ClojureHashMap.equals(value, s.value);
        }

        public int size() { return 1; }

        public INode insert_or_update(Object modifier, Object key, Object value, int hash, int hashOffset) {
            if(hash == key_hash) {
                if(ClojureHashMap.equals(this.key, key))
                    return LeafSingleNode.create(key, value, hash);
                else
                    return LeafMultipleNode.create(modifier, new Object[]{this.key,key}, new Object[]{this.value,value}, hashOffset, hash);
            } else {
                return InternalNode.create(modifier, new Object[]{this.key,key}, new Object[]{this.value,value}, hashOffset);
            }
        }

        // public boolean contains_key(Object key, int hash, int hashOffset) {
        //     return this.key.equals(key);
        // }

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
        final int key_hash;

        private LeafMultipleNode(Object modifier, Object[] ks, Object[] vs, int hash) {
            // all of the key hashes should be the same then
            key_hash = hash;
            assert(ks.length > 1);
            for(int i = 0; i < ks.length; i++) assert(ClojureHashMap.hash(ks[1]) == key_hash);
            keys = ks;
            values = vs;
            if(modifier != null) can_modify = new WeakReference<Object>(modifier);
        }

        public static INode create(Object modifier, Object[] ks, Object[] vs, int hashOffset, int hash) {
            if(ks.length == 1) {
                return LeafSingleNode.create(ks[0], vs[0], hash);
            }
            return new LeafMultipleNode(modifier, ks, vs, hash);
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
        public boolean equals(INode o, int hashOffset) {
            if(o == this) return true;
            if(!(o instanceof LeafMultipleNode)) return false;
            LeafMultipleNode m = (LeafMultipleNode)o;
            if(m.keys.length != keys.length) return false;
            for(int i = 0; i < keys.length; i++) {
                boolean found = false;
                for(int j = 0; j < m.keys.length; j++) {
                    if(ClojureHashMap.equals(keys[i], m.keys[j])) {
                        found = true;
                        if(!ClojureHashMap.equals(values[i], m.values[j])) return false;
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

        // public boolean contains_key(Object key, int hash, int hashOffset) {
        //     for(int i = 0; i < keys.length; i++)
        //         if(keys[i].equals(key))
        //             return true;
        //     return false;
        // }

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
            //int lhash = ClojureHashMap.hash(keys[0]);
            if(key_hash == hash) {
                // then this is the same hash, so we have to add it to this collection
                int index = -1;
                for(int i = 0; i < keys.length; i++) {
                    if(ClojureHashMap.equals(keys[i], key)) {
                        index = i;
                        break;
                    }
                }
                if(index != -1) {
                    if(value == null) {
                        Object[] new_keys = new Object[keys.length-1];
                        Object[] new_values = new Object[values.length-1];
                        for(int i = 0; i < new_keys.length; i++) {
                            new_keys[i] = keys[i + (i >= index ? 1 : 0)];
                            new_values[i] = values[i + (i >= index ? 1 : 0)];
                        }
                        if(can_modify) {
                            keys = new_keys;
                            values = new_values;
                            _hash = 0;
                            return this;
                        } else {
                            return new LeafMultipleNode(modifier, new_keys, new_values, hash);
                        }
                    } else {
                        if(can_modify) {
                            values[index] = value;
                            _hash = 0;
                            return this;
                        } else {
                            Object[] new_keys = new Object[keys.length];
                            Object[] new_values = new Object[values.length];
                            System.arraycopy(keys, 0, new_keys, 0, keys.length);
                            System.arraycopy(values, 0, new_values, 0, values.length);
                            new_values[index] = value;
                            return new LeafMultipleNode(modifier, new_keys, new_values, hash);
                        }
                    }
                } else {
                    if(value == null) return this; // this is a delete for something that we do not have
                    Object[] new_keys = new Object[keys.length+1];
                    Object[] new_values = new Object[values.length+1];
                    System.arraycopy(keys, 0, new_keys, 0, keys.length);
                    System.arraycopy(values, 0, new_values, 0, values.length);
                    new_keys[new_keys.length-1] = key;
                    new_values[new_values.length-1] = value;
                    if(can_modify) {
                        keys = new_keys;
                        values = new_values;
                        _hash = 0;
                        return this;
                    } else {
                        return new LeafMultipleNode(modifier, new_keys, new_values, hash);
                    }
                }
            } else {
                return InternalNode.create(modifier, new INode[]{this,LeafSingleNode.create(key, value, hash)}, new int[]{key_hash, hash}, hashOffset);
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

        public boolean equals(INode o, int hashOffset) {
            if(o == this) return true;
            if(!(o instanceof InternalNode)) {
                if(o.size() == size() && o.hashCode() == hashCode()) {
                    Iterator<MapEntry> iter;
                    try { iter = new IteratorImpl(get_node_iterator().call()); }
                    catch(Exception e) { throw new RuntimeException(e); }
                    while(iter.hasNext()) {
                        MapEntry e = iter.next();
                        Object fval = o.get_value(e.getKey(), ClojureHashMap.hash(e.getKey()), hashOffset, null);
                        if(fval != e.getValue() && !fval.equals(e.getValue()))
                            return false;
                    }
                }
                return false;
            }
            InternalNode m = (InternalNode)o;
            if(_hash != 0 && m._hash != 0 && _hash != m._hash) return false;
            if(_size != 0 && m._size != 0 && _size != m._size) return false;
            for(int i = 0; i < children.length; i++) {
                if(children[i] == null) { if(m.children[i] != null) return false; }
                else if(!children[i].equals(m.children[i], hashOffset+3)) return false;
            }
            return true;
        }

        public int hashCode() {
            if(_hash != 0) return _hash;
            int h = 0;
            for(int i = 0; i < children.length; i++)
                if(children[i] != null)
                    h ^= children[i].hashCode();
            _hash = h;
            return h;
        }

        // public boolean contains_key(Object key, int hash, int hashOffset) {
        //     int idx = hash >> hashOffset;
        //     INode c = children[idx & 7];
        //     return c != null && c.contains_key(key, hash, hashOffset+3);
        // }

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
                INode n = children[d];
                if(n == null) n = ClojureHashMap.EMPTY_INODE;
                INode nn = n.insert_or_update(modifier, key, value, hash, hashOffset+3);
                if(nn == null) {
                    int count = 0;
                    for(int i = 0; i < children.length; i++)
                        if(i != d && children[i] != null)
                            count++;
                    if(count == 0) return null;
                }
                InternalNode ret = new InternalNode(modifier);
                System.arraycopy(children, 0, ret.children, 0, 8);
                ret.children[d] = nn;
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
            return LeafSingleNode.create(key,value, hash);
        }
        //public boolean contains_key(Object key, int hash, int hashOffset) { return false; }
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

        public int hashCode() {
            return 0; // the hash code is depending on the keys which are contained, which is non in this case so it gets a zero
        }

        public boolean equals(INode o, int hashOffset) {
            return o instanceof EmptyNode;
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

    // these arrays each contain 128 random integers which are used to help
    // "randomize" the hash code of these data structures because this data
    // structure is central to Dyna's runtime performance, I am hoping that this
    // will help improve the hash of the data structures compared to just having
    // it to a few multiply and shifts.  Also these hash tables end up getting
    // nested many levels deep (In prefix tries) so if everything were to just
    // be XORed together without additional "randomization", then it would
    // likely not easily distinguish which items are contained at a given level
    // of the trie (wrt to having different hashes)

    static private final int[] hashLengthCodes = new int[] {
        1354010488,   666882026,  1644261235,   505733801, -1620672867,
        -1613092807, -1636307838,   573017211,    49787093, -1158937478,
        693157952,   930091968,   947456009,  -446424497,  -261918531,
        1086716144,  -798026765,  -915576225,   876133393, -1530401840,
        2020462433,  -642926852, -2048697536, -1021079580,  1468656921,
        -1945626244,   382452638, -1289917925, -1535446850,  -378927607,
        1507756759,  1285398752, -1369501527, -1089194309,   242885662,
        1691870554, -2002573737,  1675110565,   975554020,  1286907955,
        -1130498334,  -636677932,  -134960850,  1955062132,  -362660920,
        1814647001, -1523700186,  -185330859, -1828376059,  -564281009,
        -2055080201,  2022096163, -1696393123,  1717841403,  -302812432,
        1853339124,  -892549628,  1205387592,  -796388154, -1561407686,
        -760320996,   227132037, -1559079633,  1417362941,  1920214973,
        1648828231,  1670582671,   385206828,  -295731489,   -45115352,
        1668773725,  -519784114,  -568501455,   579807411,    80806143,
        -839953225,   -68319653,  1548674063,   580469807, -2069139142,
        -1153011473,    -4626799,   461763373,  -755946947,   719082326,
        483731367, -1228860184,  1174305761,  1126228364,    65458609,
        1377336453, -1262644309,  1465086463,   824738231,  1840639931,
        153010565, -1298465868,  1305404709,  -272531512,  -647192419,
        -468837956, -1813820571,   832800368,   -27406390, -1278501316,
        284283727, -1230221077, -1388632974,  1186212841,  -234107252,
        858406159,  -282417706,   372012048,  -180199054,  1074616697,
        130550818, -1968804716, -1132512516,   160179413, -1306777154,
        -1033675849,  1403215904, -1043975695,   235218857,  1866188495,
        -1533806926, -1530203739,    -6972277
    };

    static private final int[] hashSingleItemCodes = new int[] {
        -5574072, -1153577197, -1766919735,  1511203087,    58201498,
        -1046219181,  -852039669, -1390535230,  -281871368,  -558505161,
        1394638833, -1646014407,  -778930319, -1721454260,  -560833006,
        -760886028,  -153592854,  1784709629,   532542581,    89625058,
        829892332,  1267320794, -1065200423,   733803002, -1743603598,
        1695600846,  2111559196,  1618354480, -1169106831, -1264607120,
        -2010120110,  -758221930, -1074023631,  1109697633, -1302219143,
        565339532,  1273221610, -1804850919,  -872889601,  2121876900,
        -1663738385, -1838826226,  2133754294, -1548403810,  -332839081,
        -219702522,   367531061,  -453057335,   728499720, -1466189716,
        -145787648,  1342948593,  -129915740,  -302452619,  -477035051,
        -572267246,  1088321491, -1077248452, -1851509889, -1951206363,
        -483113519,  1165129095, -1981799194,  1214562209,    17795227,
        -142210385,   220708279,  1070698403, -1703410233,  -999167678,
        549954209,   143581287,  1952344949,  -116060101, -1379496145,
        504955744,   815853908,   140072149, -2083141743,   681266660,
        -304696378,   122501421,  -967178721,  1122888997,   533517780,
        966482624,   475666273,  2030116328,   -77673271,  -148427209,
        873600273, -1813541622,  -485160296,  1802232293, -1270159212,
        791128671,   983753641, -1583413696,  1585188990,  -181623592,
        -1379621344, -1772104292,  1132101014,   562963600,  -266422394,
        -1147845242,   -42297959,  -492850748,   262785288,   890739783,
        -151956963,  -569138263,   779696843,   776367356, -2013530678,
        226559799,  -524189906, -2061762632,  -728666062,  2145500809,
        1654536520,  2056762068,   454245450,  2144029937,   723377252,
        108663194,  1130076754, -1696189521
    };

    static private final int[] hashSingleItemCodes2 = new int[] {
        -1296884838,   843082774,   564221475,   301479376,  -196999787,
        1355343325,   -79727894,   207798629, -1198662470, -1348932038,
        1514962866, -1854271264,  -911778533,   299613646,  2140331275,
        127296863,  1435433424,  1843559164,   508179692,  -191331121,
        -1751034738,  1601903781,   803223792,  1542961871, -1646160204,
        -785444177,  1419811831, -1308535008,   976458840, -2147313958,
        2128947067, -2039462216,  1079238424,   410102799,   874884012,
        -1643478651,  2033879526,  1287501109,   832922874, -1039798522,
        -1875233345, -1139556883,  -241654799,  1692261968, -1334655824,
        1281552924,   266206591,  1581087025,  -736770164,  1212943069,
        -1332273202,   406833045,   169200311,   495219322,  -886002811,
        2071877807, -1491532510, -1166136944, -2140137967, -1025837256,
        -747375099,   833198062,   570093104,   164062665,  1510939084,
        2137350368,  1738101820,  -746882285,   266942716,  -543467085,
        1102731525,   828976543,  -330507466,  -671908673,  2047443395,
        -1193192420,  -221791695,  2032443427,   265070668,   254102332,
        837183962, -1961456305,  1834359282,  1598809423,  -238728019,
        -1993915038,  1061223398,   153111351, -2065257205,   -22712616,
        -148304969,  1042969339, -1912366630,   897800411,  2120380468,
        2024480543, -1639385168,    32407914,   238723520,  1057847484,
        236559228,   400681944, -1400674361,  1884386107,  2047360415,
        -1665380378,    73924110,   470190876,  -649468744,  -790108427,
        -1401171152, -1376235164,  1282085155,  -167108532,  -596571534,
        183987855,  1581584491, -1894063208, -1446339145,  2063108140,
        -422011787,  -821258974,   965063325,  -857335669,  1315267453,
        474923448,  1128132417,  -797171661
    };

    static private final int[] hashPairCodes = new int[] {
        -1420205339,  -416724138,  1644614752,  1129610392, -1359505267,
        -379617818, -1255562079,   556754590, -1877963157,  2113765247,
        619594581,  1833261861,  1275040723,  -528682267, -2032054711,
        1799743290,  1515710657,  -663544017,  1301871604,   923979989,
        -863512395, -1911702930,   393909885,  1657968659, -1392500480,
        1261248153, -1985017501, -1195027608,  1423905859, -1810306142,
        -1293790227,   675426322,  1979823144,   707793099,  1335540451,
        751645561,  -146662053, -1536476652,  1204499094,   997067359,
        -254934898, -1973443019,   458243948,  1901314953, -1237530348,
        399973306,  1472723045, -1824860598,  -751299115, -1048694512,
        -1039420511,   274938216,  -218616570,  1893041393,    28604199,
        1979863658,   677640715,  1233907320, -1057725016,  1383440496,
        207233331, -1166679806, -1868978214, -1784163552,  1228029323,
        -798167893,  1879937084,  -510467188,  1854180080,  -491003161,
        -1602729789, -1982898345,   -71180648,  1300088432, -1877711451,
        1805775756,  1526992084,    87306734, -1064169051,   686421189,
        1456462083,  1093411743,  -554367703,  1326579444,  -734789491,
        285643523,  1794951534,    99506091, -1824203050,   829666727,
        -1594714478,  -679299198,  1108185498,  1008150607,  1370809362,
        -794087698,  1107785366, -2093090368, -1229611460, -1832612874,
        1314745083,  -275293023,  1521760481,   796720081, -1875196919,
        -1045189290, -1356960629,  -549734405,   568903828,  -625827013,
        -2140460002,  1047297794,  1743323927,  -550254465,  -517150809,
        -1586343950,   227719426,  1575351969, -1020346470,  2016728818,
        188025022, -1009936087,  1598132647, -1363466233,  -910402339,
        -1284995417,  2126273784,  1497582889
    };
}
