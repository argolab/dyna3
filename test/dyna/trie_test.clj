(ns dyna.trie-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.utils :refer :all])
  (:require [dyna.prefix-trie :refer :all])
  (:import [dyna.prefix_trie IPrefixTrie PrefixTrie]))




(deftest small-trie
  (let [trie (PrefixTrie. 2 0 {:a {:b [1]
                                   :c [2 3]}})
        values (trie-get-values trie nil)
        values-1a (into #{} (trie-get-values trie [:a nil]))
        values-1c (into #{} (trie-get-values trie [:c nil]))
        values-2b (into #{} (trie-get-values trie [nil :b]))]
    (is (= values-1a #{[(list :a :c) 3] [(list :a :c) 2] [(list :a :b) 1]}))
    (is (= values-1c #{}))
    (is (= values-2b #{[(list :a :b) 1]}))
    (is (instance? clojure.lang.LazySeq values))))

(deftest update-trie
  (let [trie (PrefixTrie. 2 0 {:a {:b [1]
                                   :c [2 3]}})
        trie2 (assoc trie [:foo :bar] 99)

        values (into #{} (trie-get-values trie2 nil))]
    (is (= values #{[(list :a :c) 3] [(list :foo :bar) 99] [(list :a :c) 2] [(list :a :b) 1]}))))

(deftest nil-val-trie
  (let [trie (PrefixTrie. 2 0x1 {:a {:b [1]
                                     :c [2 3]}
                                 nil {:b [4]
                                      :d [5]}})
        values (into #{} (trie-get-values trie nil))
        values-a1 (into #{} (trie-get-values trie [:a nil]))
        values-b2 (into #{} (trie-get-values trie [nil :b]))]
    (is (= values #{[(list nil :b) 4] [(list nil :d) 5] [(list :a :c) 3] [(list :a :c) 2] [(list :a :b) 1]}))
    (is (= values-a1 #{[(list nil :b) 4] [(list nil :d) 5] [(list :a :c) 3] [(list :a :c) 2] [(list :a :b) 1]}))
    (is (= values-b2 #{[(list nil :b) 4] [(list :a :b) 1]}))))

(deftest merge-tries
  (let [trie1 (PrefixTrie. 2 0 {:a {:b [1]
                                    :c [2 3]}})
        trie2 (PrefixTrie. 2 0 {:a {:b [3]
                                    :d [4]}})
        trie (trie-merge trie1 trie2)
        values (into #{} (trie-get-values trie nil))]
    (is (= values #{[(list :a :d) 4] [(list :a :b) 3] [(list :a :c) 3] [(list :a :c) 2] [(list :a :b) 1]}))))


;; want the order as well as the "type" at the leaf to not matter wrt
(deftest hash-trie-different-order
  (let [trie1 (PrefixTrie. 2 0 {:a {:b [1 2 3]}})
        trie2 (PrefixTrie. 2 0 {:a {:b (list 3 1 2)}})]
    (assert (= (hash trie1) (hash trie2)))
    (assert (= trie1 trie2))
    ))


(deftest trie-map-values-test
  (let [trie1 (PrefixTrie. 2 0x1 {:a {:b [1]
                                      :c [2 3]}
                                  nil {:b [4]
                                       :d [5]}})
        trie2 (trie-map-values trie1 nil (fn [a b] (* 2 b)))]
    (is (= (.root trie2)
           {:a {:b [2]
                :c [4 6]}
            nil {:b [8]
                 :d [10]}}))))
