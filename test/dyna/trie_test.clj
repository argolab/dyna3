(ns dyna.trie-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.prefix-trie :refer :all])
  (:import [dyna.prefix_trie IPrefixTrie PrefixTrie]))


(deftest make-trie
  (make-prefixtrie 10))

(deftest small-trie
  (let [trie (PrefixTrie. 2 0 nil {:a {:b [1]
                                       :c [2 3]}})
        values (get-values trie nil)
        f1 (filter-key trie [:a nil])
        values-f1 (get-values f1 nil)
        f2 (insert-val trie [:a :d] 7)
        values-f2 (get-values f2 nil)
        ]

    (debug-repl))
  )
