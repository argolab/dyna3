(ns dyna.prefix-trie
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr])
  ;(:import [dyna IPrefixTrie])
  )


;; the data structure could be represented as differented nested objects rather
;; than having a single trie which represents everything?  The question would
;; then be updating the nested structure.  it seems that vectors have some way
;; in which they can replace some of the elements with a masked array.


;; this file is not used yet


;; (gen-interface
;;  :name dyna.IPrefixTrie
;;  :extends [clojure.lang.ILookup]
;;  :methods [[get [Object] Object]
;;            [set [Object Object] "Ldyna.IPrefixTrie;"]
;;            ])


;; example structure of the trie
#_({:a {:b [val1 val2]}})

(defn- merge-map-arity [arity & args]
  (if (= arity 0)
    (apply concat args)
    (apply merge-with (partial merge-map-arity (- arity 1)) args)))

(defn- equal-tries [arity map1 map2]
  (if (identical? map1 map2)
    true
    (if (or (empty? map1) (empty? map2))
      (and (empty? map1) (empty? map2))
      (if (= arity 0)
        (= (frequencies map1) (frequencies map2)) ;; then this needs to check that the same number of elements appear, but the order doesn't matter
        ;; then this needs to compare that the inner elements are equal to eachother
        (and (= (count map1) (count map2))
             (every? #(equal-tries (- arity 1) (get map1 %) (get map2 %)) (keys map1)))))))

;; the elements in the leaf of the trie should not matter about the order, so this is
(defn- hash-tries [arity node]
  (if (= arity 0)
    (reduce bit-xor (map hash node))
    (reduce unchecked-add-int (map #(bit-xor (hash (first %)) (hash-tries (- arity 1) (second %))) node))))

(defsimpleinterface IPrefixTrie
  (trie-get-values-collection [key])  ;; return the values associated with a given key together
  (trie-get-values [key])  ;; return the values associated with a given key seperatly
  (trie-map-values [key ^clojure.lang.IFn map-fn])
  (trie-map-collection [key ^clojure.lang.IFn map-fn])
  ;; (filter-key [key])
  ;; (clear-filter [])
  (trie-insert-val [key val])
  (trie-update-collection [key ^clojure.lang.IFn update-fn])
  (trie-merge [^dyna.prefix_trie.IPrefixTrie other])

  (trie-delete-matched [key]))

;; (intern 'dyna.rexpr 'check-argument-prefix-trie (fn [x] (instance? IPrefixTrie x)))

(defn check-argument-prefix-trie [x] (instance? IPrefixTrie x))

(deftype PrefixTrie [^int arity
                     ^long contains-wildcard
                     ;; ^int filter-arity
                     ;; filter ;; a tuple of which keys are already known or the value nil indicating that there is nothing
                     root]
  IPrefixTrie
  (trie-get-values-collection [this key]
    (let [key (if (nil? key) (repeat arity nil) key)]
      (assert (= (count key) arity))
      ((fn rec [key-so-far key-query node]
         (if (empty? key-query)
           (let [k (reverse key-so-far)]
             [[k node]])
           (let [key (first key-query)
                 look-keys (if-not (nil? key)
                             [key nil]
                             (keys node))
                 next-key (rest key-query)]
             (apply concat (for [k look-keys]
                             (let [v (get node k)]
                               (if-not (nil? v)
                                 (lazy-seq (rec (cons k key-so-far)
                                                next-key
                                                v))
                                 ())))))))
       () key root)))

  (trie-get-values [this key]
    (for [[k node] (trie-get-values-collection this key)
          val node]
      [k val]))

  (trie-map-collection [this key0 map-fn]
    (let [key (if (nil? key0) (repeat arity nil) key0)]
      (assert (= (count key) arity))
      (let [new-root ((fn rec [key-so-far key-query node]
                        (if (empty? key-query)
                          (vec (map-fn (reverse key-so-far) node))
                          (let [cur-key (first key-query)
                                rest-key (rest key-query)
                                key-so-far2 (cons cur-key key-so-far)]
                            (into {} (remove empty? (map (fn [[key x]]
                                                           (if (or (nil? cur-key)
                                                                   (nil? key)
                                                                   (= cur-key key))
                                                             (let [v (rec key-so-far2 rest-key x)]
                                                               (when-not (empty? v)
                                                                 [key v]))
                                                             [key x] ;  this is not mapped, so just keep it the same
                                                             ))
                                                         node))))))
                      () key root)]
        (PrefixTrie. arity contains-wildcard new-root))))

  (trie-map-values [this key map-fn]
    (trie-map-collection this key (fn [rk col]
                                    (remove nil? (map #(map-fn rk %) col)))))

  ;; Question: should the mapping of a value have that this goes through everything or that it will just map the relevant keys
  #_(trie-map-values [this key map-fn]
    ;; construct a new trie where all of the values which match have been passed to the mapper function
    (let [key (if (nil? key) (repeat arity nil) key)]
      (assert (= (count key) arity))
      (let [new-root ((fn rec [key-so-far key-query node]
                        (if (empty? key-query)
                          (vec (remove nil? (map #(map-fn [(reverse key-so-far) %]) node)))
                          (let [cur-key (first key-query)
                                rest-key (rest key-query)
                                key-so-far (cons cur-key key-so-far)]
                            (into {} (remove empty? (map (fn [[key x]]
                                                           (if (or (nil? cur-key)
                                                                   (= cur-key key)
                                                                   (nil? key))
                                                             (let [v (rec key-so-far rest-key x)]
                                                               (when-not (empty? v)
                                                                 [key v])) ;; remap this value
                                                             [key x] ;; we are not mapping these values, so keep the same element in the map
                                                             ))
                                                         node)))))
                          ;; then this is going to
                          )
                      () key root)]
        (PrefixTrie. arity contains-wildcard new-root))))

  (trie-update-collection [this key update-fn]
    (assert (= (count key) arity))
    (PrefixTrie. arity
                 (apply bit-or contains-wildcard (map (fn [[idx v]] (if (nil? v) (bit-shift-left 1 idx) 0))
                                                      (zipmap (range) key)))
                 (update-in root key update-fn)))

  (trie-insert-val [this key val]
    (assert (= (count key) arity)) ;; there should be some function which remaps the key into what the filter is going to construct
    (trie-update-collection this key (fn [prev-val]
                                       (conj (or prev-val []) val))))

  (trie-merge [this other]
    (assert (= arity (.arity other)))
    (PrefixTrie. arity
                 (bit-or contains-wildcard (.contains-wildcard other))
                 (merge-map-arity arity root (.root other))))

  (trie-delete-matched [this key]
    (???)
    #_(if (or (nil? key) (every? nil? key))
        (PrefixTrie. arity nil) ;; just delete everything, so return something that is new
      (do
        (assert (= arity (count key)))
        (PrefixTrie. arity (fn rec [key-query node]
                             (if (or (empty? key-query) (every? nil? key-query))
                               node
                               ;; then we have to filter out the map
                               (let [kf (first key-query)
                                     kt (rest key-query)]
                                 (into {} (map (fn [[k v]]
                                                 (???)))))
                               ))))
      ))

  Object
  (toString [this] (str "Prefix trie " arity))
  (equals [this other]
    ;; if this is an immutable structure, then it is really jst if this is going to have some of the
    (or (identical? this other)
        (and (instance? PrefixTrie other)
             (= arity (.arity ^PrefixTrie other))
             (equal-tries arity root (.root ^PrefixTrie other)))))

  (hashCode [this]
    (unchecked-add-int arity (hash-tries arity root)))

  clojure.lang.ILookup
  (valAt [this key] (.valAt this key nil))
  (valAt [this key notfound]
    (assert (seqable? key))
    (let [ret (map second (trie-get-values key))]
      (if (empty? ret) [notfound] ret)))

  clojure.lang.Seqable
  (seq [this] (trie-get-values this nil))

  clojure.lang.IPersistentCollection
  (count [this] (count (trie-get-values this)))
  (cons [this other] (???))
  (equiv [^IPrefixTrie this other]
    (.equals this other))

  clojure.lang.Associative
  (containsKey [this key]
    (assert (seqable? key))
    (not (empty? (trie-get-values key))))
  (entryAt [this key]
    (into {} (trie-get-values this )))
  (assoc [this key val]
    (trie-insert-val this key val)))


;; (defn make-prefixtrie [arity]
;;   (???))

;; (defn zip-tries [a b]
;;   nil ;; return some iterator over the two tries at the same time
;;   ;; tihs will need to
;;   )
