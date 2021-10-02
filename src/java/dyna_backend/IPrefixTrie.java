package dyna_backend;

import clojure.lang.Associative;

interface IPrefixTrie extends Associative {

    // the arity of the object as presented
    int arity();

    // the arity of the object without the additional filtered objects
    int true_arity();

    // add to the the filter, the keys should match the arity
    IPrefixTrie filter(Object keys);

}
