(ns dyna.prefix-trie
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr])
                                        ;(:import [dyna IPrefixTrie])
  (:import [dyna ClojureUnorderedVector ClojureHashMap])
  )



(defn trie-hash-map [& args]
  (ClojureHashMap/createFromSeq args))

(defn- trie-update-in
  {:static true}
  ([m ks f & args]
   (let [up (fn up [m ks f args]
              (let [[k & ks] ks]
                (ClojureHashMap/create
                 (if ks
                   (assoc m k (up (get m k) ks f args))
                   (assoc m k (apply f (get m k) args))))))]
     (up m ks f args))))

(defn- trie-assoc-in
  {:static true}
  [m [k & ks] v]
  (ClojureHashMap/create
   (if ks
     (assoc m k (trie-assoc-in (get m k) ks v))
     (assoc m k v))))

(defn- merge-map-arity [arity & args]
  (if (= arity 0)
    (ClojureUnorderedVector/concat args)
    (let [f (first args)]
      (apply merge-with (partial merge-map-arity (- arity 1)) (if (nil? f) ClojureHashMap/EMPTY f) (rest args)))))

(defsimpleinterface IPrefixTrie
  (trie-arity [])
  (trie-wildcard [])
  (trie-root [])
  (trie-get-values-collection [key])  ;; return the values associated with a given key together
  (trie-get-values [key])  ;; return the values associated with a given key seperatly

  (trie-get-values-collection-no-wildcard [key])

  ;; return a trie with only the values which match the key changed.  Values
  ;; which do not match the key will be left unchanged and still in the trie.
  ;; unchanged internal structure of the tries will be shared (the internal
  ;; structure is immutable hash maps)
  (trie-map-values [key ^clojure.lang.IFn map-fn])
  (trie-map-collection [key ^clojure.lang.IFn map-fn])

  ;; return a trie with only the subset of values which match the key as well as run the matching function over the values
  (trie-map-collection-subset [key ^clojure.lang.IFn map-fn])
  (trie-map-values-subset [key ^clojure.lang.IFn map-fn])

  ;; (filter-key [key])
  ;; (clear-filter [])
  (trie-insert-val [key val])
  (trie-update-collection [key ^clojure.lang.IFn update-fn])
  (trie-merge [^dyna.prefix_trie.IPrefixTrie other])

  (trie-delete-matched [key])
  (trie-delete-key [key])

  ;; this is going to have to return an iterator of the subset of values which map to something
  ;; if there is something about wehich expression might have this
  (trie-progressive-iterator [key])

  (trie-reorder-keys [new-order])

  (trie-reorder-keys-subselect [new-order known-values])

  ;; any key which is non-nil will be selected to that particular value
  ;(trie-select-subkeys [key])
  )

;; (intern 'dyna.rexpr 'check-argument-prefix-trie (fn [x] (instance? IPrefixTrie x)))

(defn check-argument-prefix-trie [x] (instance? IPrefixTrie x))

(declare make-PrefixTrie)

(deftype PrefixTrie [^int arity
                     ^long contains-wildcard
                     ;; ^int filter-arity
                     ;; filter ;; a tuple of which keys are already known or the value nil indicating that there is nothing
                     root
                     ;^{:tag int :unsynchronized-mutable true} hashCodeCache
                     ]
  IPrefixTrie
  (trie-arity [this] arity)
  (trie-wildcard [this] contains-wildcard)
  (trie-root [this] root)
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
             (apply concat (for [k look-keys]   ;;; TODO: this should use a lazy iterator over this, maybe something like lazy-cat
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

  (trie-get-values-collection-no-wildcard [this key]
    (let [key (if (nil? key) (repeat arity nil) key)]
      (assert (= (count key) arity))
      ((fn rec [key-so-far key-query node]
         (if (empty? key-query)
           [[(reverse key-so-far) node]]
           (let [key (first key-query)
                 look-keys (if (nil? key) [nil] [nil key])
                 next-key (rest key-query)]
             (apply concat (for [k look-keys]
                             (let [v (get node k)]
                               (if-not (nil? v)
                                 (lazy-seq (rec (cons k key-so-far) next-key v)))))))))
       () key root)))

  (trie-map-collection [this key0 map-fn]
    (let [key (if (nil? key0) (repeat arity nil) key0)]
      (assert (= (count key) arity))
      (let [new-root ((fn rec [key-so-far key-query node]
                        (if (empty? key-query)
                          (ClojureUnorderedVector/create (map-fn (reverse key-so-far) node))
                          (let [cur-key (first key-query)
                                rest-key (rest key-query)
                                ;key-so-far2 (cons cur-key key-so-far)
                                ]
                            (into ClojureHashMap/EMPTY
                                  (remove empty? (map (fn [[key x]]
                                                        (if (or (nil? cur-key)
                                                                (nil? key)
                                                                (= cur-key key))
                                                          (let [v (rec (cons key key-so-far) rest-key x)]
                                                            (when-not (empty? v)
                                                              [key v]))
                                                          [key x] ;  this is not mapped, so just keep it the same
                                                          ))
                                                      node))))))
                      () key root)]
        (make-PrefixTrie arity contains-wildcard new-root))))

  (trie-map-values [this key map-fn]
    (trie-map-collection this key (fn [rk col]
                                    (remove nil? (map #(map-fn rk %) col)))))

  (trie-map-collection-subset [this key0 map-fn]
    (let [key (if (nil? key0) (repeat arity nil) key0)]
      (assert (= (count key) arity))
      (let [new-root ((fn rec [key-so-far key-query node]
                        (if (empty? key-query)
                          (ClojureUnorderedVector/create (map-fn (reverse key-so-far) node))
                          (let [cur-key (first key-query)
                                rest-key (rest key-query)
                                ;key-so-far2 (cons cur-key key-so-far)
                                ]
                            (into ClojureHashMap/EMPTY
                                  (remove empty? (if (nil? cur-key)
                                                   (for [[k v] node
                                                         :let [r (rec (cons k key-so-far) rest-key v)]
                                                         :when (not (empty? r))]
                                                     [k r])
                                                   (for [k [nil cur-key]
                                                         :let [v (get node k)]
                                                         :when (not (nil? v))]
                                                     (let [r (rec (cons k key-so-far) rest-key v)]
                                                       (when-not (empty? r)
                                                         [k r])))))))))
                      () key root)]
        ;; technically the contains wildcard could get remapped here
        (make-PrefixTrie arity contains-wildcard new-root))))

  (trie-map-values-subset [this key map-fn]
    (trie-map-collection-subset this key (fn [rk col]
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
        (make-PrefixTrie arity contains-wildcard new-root))))

  (trie-update-collection [this key update-fn]
    (assert (and (= (count key) arity)))
    (make-PrefixTrie arity
                 (reduce bit-or contains-wildcard (map (fn [[idx v]] (if (nil? v) (bit-shift-left 1 idx) 0))
                                                       (zipmap (range) key)))
                 (if (> arity 0)
                   (trie-update-in root key #(ClojureUnorderedVector/create (update-fn %)))
                   (ClojureUnorderedVector/create (update-fn root)))))

  (trie-insert-val [this key val]
    (assert (= (count key) arity)) ;; there should be some function which remaps the key into what the filter is going to construct
    (trie-update-collection this key (fn [prev-val]
                                       (conj (or prev-val []) val))))

  (trie-merge [this other]
    (assert (= arity (trie-arity other)))
    (make-PrefixTrie arity
                 (bit-or contains-wildcard (trie-wildcard other))
                 (merge-map-arity arity root (trie-root other))))

  (trie-delete-matched [this key]
    (if (or (nil? key) (every? nil? key))
      (make-PrefixTrie arity 0 nil) ;; this matches everything, so return an empty trie
      (make-PrefixTrie arity contains-wildcard
                   ((fn rec [key-query node]
                      (if (empty? key-query)
                        nil
                        (let [[f & r] key-query]
                          (if (nil? f)
                            (into ClojureHashMap/EMPTY
                                  (remove nil? (for [[k v] node]
                                                 (let [e (rec r v)]
                                                   (when-not (nil? e)
                                                     [k e])))))
                            (into ClojureHashMap/EMPTY
                                  (remove nil? (for [[k v] node]
                                                 (if (= k f)
                                                   (let [e (rec r v)]
                                                     (when-not (nil? e)
                                                       [k e]))
                                                   [k v]))))))))
                    key root))))

  (trie-delete-key [this key]
    (assert (= arity (count key)))
    (make-PrefixTrie arity contains-wildcard
                 ((fn rec [key-query node]
                    (if (empty? key-query)
                      nil)
                    (if-not (contains? node (first key-query))
                      node
                      (let [kk (first key-query)
                            nv (rec (next key-query) (get node kk))
                            nm (if (nil? nv) (dissoc node kk) (assoc node kk nv))]
                        (when-not (empty? nm)
                          nm))))
                  key root)))

  (trie-progressive-iterator [this key0]
    (let [key (if (nil? key0) (repeat arity nil) key0)]
      (assert (= arity (count key)))
      ((fn rec [key-so-far key-query node]
         ;; this should still run against the values which find this expression.
         ;; in the case that something would have that the values
         ;; there should be some continuation which is passed along
         (if (empty? key-query)
           node
           (let [cur-key (first key-query)
                 rest-key (rest key-query)
                 key-so-far2 (cons cur-key key-so-far)]
             (if (nil? cur-key)
               ;;  then this is going to return all of the possible values, but that should be done as an iterator
               ;; what is going to happen in the case that there is something that represents the empty set
               (for [[key val] node]
                 ;; this can return a function for the possible values.
                 ;; if there is something which would hold what is going
                 [key #(rec key-so-far2 rest-key val)])
               ;; this only needs to return the key and nil
               ;; in the case that there

               (???)
               )
             ))
         (???)
         )
       () key root)))

  (trie-reorder-keys [this new-order]
    ;; the arity between the keys could include adding in new keys.  In which case this is going to have to identify new values for this
    (dyna-assert (>= (count new-order) arity))
    (if (= new-order (vec (range arity)))
      this  ;; there is no change so just return this without making any changes
      (let [new-contains-wildcard (reduce bit-or 0 (map (fn [i] (if (or (nil? (nth new-order i))
                                                                        (not= 0 (bit-and (bit-shift-left 1 (nth new-order i)) contains-wildcard)))
                                                                  (bit-shift-left 1 i)
                                                                  0))
                                                        (range (count new-order))))
            new-root (volatile! ClojureHashMap/EMPTY)]
        (doseq [[key col] (trie-get-values-collection this nil)]
          (let [new-key (vec (map (fn [i] (if (nil? i) nil (nth key i))) new-order))]
            (vswap! new-root trie-assoc-in new-key col)))
        (make-PrefixTrie (count new-order) new-contains-wildcard @new-root))))

  (trie-reorder-keys-subselect [this new-order known-values]
    (if (every? nil? known-values)
      (trie-reorder-keys this new-order)
      (let [new-root (volatile! ClojureHashMap/EMPTY)
            new-contains-wildcard (reduce bit-or 0 (map (fn [[new-i old-i]]
                                                          (if (not= 0 (bit-and (bit-shift-left 1 old-i) contains-wildcard))
                                                            (bit-shift-left 1 new-i)
                                                            0))
                                                        (zipseq (range) new-order)))]
        (dyna-assert (= arity (+ (count (remove nil? known-values)) (count (remove nil? new-order)))))
        (doseq [[key col] (trie-get-values-collection this known-values)]
          (let [new-key (vec (map (fn [i] (if (nil? i) nil (nth key i))) new-order))]
            (vswap! new-root trie-assoc-in new-key col)))
        (make-PrefixTrie (count new-order) new-contains-wildcard @new-root))))

  #_(trie-select-subkeys [this key]
    (assert (= (count key) arity))
    (let (= new-order ))
    (let [new-arity (count (filter nil? key))]
      (if (= new-arity arity)
        this ;; then nothing is projected out
        (let [r (fn rec [] )]))
      )
    )

  Object
  (toString [this]
    (println "===================== prefix trie to string called")
    (str "Prefix trie " arity))
  (equals [this other]
    ;; if this is an immutable structure, then it is really jst if this is going to have some of the
    (or (identical? this other)
        (and (instance? PrefixTrie other)
             (= arity (.arity ^PrefixTrie other))
             (= contains-wildcard (.contains-wildcard ^PrefixTrie other))
             (= root (.root ^PrefixTrie other))  ;; the equals now should handle things being out of order
                                        ;(equal-tries arity root (.root ^PrefixTrie other))
             )))

  (hashCode [this]
    #_(when (= hashCodeCache 0)
        (set! hashCodeCache (unchecked-add-int arity (hash-tries arity root))))
                                        ;hashCodeCache
    (unchecked-add-int arity (hash root)))

  clojure.lang.ILookup
  (valAt [this key] (.valAt this key nil))
  (valAt [this key notfound]
    (assert (seqable? key))
    (let [ret (map second (trie-get-values this key))]
      (if (empty? ret) [notfound] ret)))

  clojure.lang.Seqable
  (seq [this] (trie-get-values this nil))

  clojure.lang.IPersistentCollection
  (count [this] (count (trie-get-values this nil)))
  (cons [this other] (???))
  (equiv [^IPrefixTrie this other]
    (.equals this other))

  clojure.lang.Associative
  (containsKey [this key]
    (assert (seqable? key))
    (not (empty? (trie-get-values this key))))
  (entryAt [this key]
    (into {} (trie-get-values this nil)))
  (assoc [this key val]
    (trie-insert-val this key val)))

(defn make-PrefixTrie [arity wildcard root]
  ;; check that we have the right internals for now
  (dyna-slow-check
   (if (> arity 0)
     ((fn rec [d n wild]
        (if (= d 0)
          (assert (instance? ClojureUnorderedVector n))
          (do
            (assert (or (= 1 (bit-and 1 wild)) (not (contains? n nil))))
            (dyna-assert (or (nil? n) (instance? ClojureHashMap n)))
            (doseq [v (vals n)]
              (rec (- d 1) v (bit-shift-right wild 1))))))
      arity root wildcard)
     (assert (or (nil? root) (instance? ClojureUnorderedVector root)))))
  (PrefixTrie. arity wildcard root))

;; the prefix trie is going to require that the clojure hash type maps are also printable, but this does not have a print-dup method...
#_(defmethod print-dup PrefixTrie [^PrefixTrie this ^java.io.Writer w]
    (.write w (str "(dyna.prefix-trie/make-PrefixTrie "
                   (.arity this) " "
                   (.contains-wildcard this) " "))
    (print-dup (.root this) w)
    (.write w ")"))

(defmethod print-method PrefixTrie [^PrefixTrie this ^java.io.Writer w]
  (.write w (str "(PrefixTrie "
                 (.arity this) " "
                 (.contains-wildcard this) " "))
  (print-method (.root this) w)
  (.write w ")"))

;; (defn make-prefixtrie [arity]
;;   (???))

;; (defn zip-tries [a b]
;;   nil ;; return some iterator over the two tries at the same time
;;   ;; tihs will need to
;;   )


(defn tries-differences [^PrefixTrie a ^PrefixTrie b]
  ;; return the elements that are contained in one trie but not the other
  ;; I suppose that this is going to have to respect the filter as well?  Otherwise this is not going to find which of the
  (assert (= (.arity a) (.arity b)))
  ((fn rec [remains an bn]
     (cond
       (or (identical? an bn) (= an bn))  ()
       (= remains 0)  [[() an bn]]
       (nil? bn) [[() an nil]]
       (nil? an) [[() nil bn]]

       :else
       (concat (for [[k v] an
                     [kp av bv] (rec (- remains 1) v (get bn k))]
                 [(cons k kp) av bv])
               (for [[k v] bn
                     :when (not (contains? an k))
                     [kp av bv] (rec (- remains 1) nil v)]
                 [(cons k kp) av bv])))
     )
   (.arity a) (.root a) (.root b)))
