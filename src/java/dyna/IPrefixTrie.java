package dyna;

import clojure.lang.Associative;

interface IPrefixTrie extends Associative {

    // the arity of the object as presented
    int arity();

    // the arity of the object without the additional filtered objects
    int true_arity();

    // add to the the filter, the keys should match the arity
    IPrefixTrie filter(Object keys);

    // run over all of the values and apply the function.  A new prefix trie is created and returned as a result
    IPrefixTrie update_map_all(clojure.lang.IFn fn);

    // join this trie with the selector argument.  Run the fn with the value for
    // this trie, the selector trie and then return a new trie which contains
    // only the selected keys updated
    IPrefixTrie update_map_subset(IPrefixTrie subset_selector, clojure.lang.IFn fn);

    IPrefixTrie zip_tries(IPrefixTrie other);


    IPrefixTrie assoc(Object key, Object val);

    Object valAt(Object key);// { return valAt(key, null); }
    Object valAt(Object key, Object notFound);

    int count();// { throw RuntimeException("Not implemented"); }

    IPrefixTrie cons(Object other);

    boolean equiv(Object other);

}
