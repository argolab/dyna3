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

(defsimpleinterface IPrefixTrie
  (get-values [key])
  (map-values [key map-fn])
  ;; (filter-key [key])
  ;; (clear-filter [])
  (insert-val [key val])
  (merge-tries [^dyna.prefix_trie.IPrefixTrie other])
  ;(assoc-map-vals )
  )

(intern 'dyna.rexpr 'check-arguments-prefix-trie (fn [x] (instance? IPrefixTrie x)))

(deftype PrefixTrie [^int arity
                     ;; ^int filter-arity
                     ;; filter ;; a tuple of which keys are already known or the value nil indicating that there is nothing
                     root]
  IPrefixTrie
  (get-values [this key]
    (assert (= (count key) arity))
    ((fn rec [key-so-far key-query node]
       (if (empty? key-query)
         (let [k (reverse key-so-far)]
           (for [val node]
             [k val]))
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
     () key root))

  #_(get-values [this key]
    (let [key (if (nil? key) (repeat (- arity filter-arity) nil) key)]
      (assert (= (+ (count key) filter-arity) arity)) ;; otherwise there is something which
      ((fn rec [key-so-far key-query cur-filter node]
         (if (and (empty? key-query) (empty? cur-filter))
           (for [val node]
             ;; the node can will be a list of values at the end
             [(reverse key-so-far) val])
           (let [filter-first (first cur-filter)
                 [cur-key next-key] (if (nil? filter-first)
                                      [(first key-query) (rest key-query)]
                                      [filter-first key-query])
                 next-filter (rest cur-filter)]
             (if-not (nil? cur-key)
               ;; get the relevant entries for tihs
               (let [nil-val (get root nil) ;; this is the default
                     key-val (get root cur-key) ;; this is the value that is returned for the current key
                     ]
                 (cond (and (not (nil? nil-val)) (not (nil? key-val))) (lazy-cat (rec (cons cur-key key-so-far) next-key next-filter key-val)
                                                                                 (rec (cons nil key-so-far)     next-key next-filter nil-val))
                       (not (nil? key-val)) (rec (cons cur-key key-so-far) next-key next-filter key-val)
                       (not (nil? nil-val)) (rec (cons nil key-so-far)     next-key next-filter nil-val)
                       :else []))
               ;; then we need to return a sequence over all of the keys which are contained at this level
               (apply concat
                      (for [k (keys node)]
                        (lazy-seq (rec (cons k key-so-far) next-key next-filter (get node k)))))
               ))))
       () key filter root)))

  (map-values [this key map-fn]
    ;; construct a new trie where all of the values which match have been passed to the mapper function
    ((fn rec [key-so-far key-query cur-filter node]

       (???))
     () key filter root))

  ;; (assoc-map-vals [this key val]
  ;;   (let [kvm (into {} (partition 2 key+vals))
  ;;         new-root ((fn rec [key-so-far key-query cur-filter node]

  ;;                     )
  ;;                   ()
  ;;                   )

  ;;         ]
  ;;     ))

  (insert-val [this key val]
    (assert (= (count key) arity)) ;; there should be some function which remaps the key into what the filter is going to construct
    (PrefixTrie. arity
                 (update-in root key (fn [prev-val]
                                       (conj (or prev-val []) val)))))

  #_(filter-key [this key]
    ;; return a trie where there is a new filter which is applied
    (let [new-filter (loop [pf ()
                            f filter
                            k key]
                       (if (and (empty? f) (empty? k))
                         (reverse pf)
                         (if-not (nil? (first f))
                           (recur (conj pf (first f))
                                  (rest f)
                                  k)
                           (recur (conj pf (first k))
                                  (rest f)
                                  (rest k)))))
          filter-arity (count (remove nil? new-filter))]
      (assert (= (count new-filter) arity))
      (PrefixTrie. arity filter-arity new-filter root)))

  #_(clear-filter [this]
    (PrefixTrie. arity 0 nil root))

  (merge-tries [this other]
    (assert (= arity (.arity other)))
    ;; (assert (nil? filter))
    ;; (assert (nil? (.filter other)))
    (???)
    #_(let [mmf (fn mmf [ra]
                (if (= ra 0)
                  #(vec (concat %1 %2)) ;; do we care about this being a vector or a list? can we work with either
                  (fn [a b]
                    (merge-with (mmf (- ra 1)) a b))))]
      (PrefixTrie. arity filter-arity filter
                   ((mmf arity) root (.root other)))))

  Object
  (toString [this] (str "Prefix trie " arity))
  (equals [this other]
    (or (identical? this other)
        (and (instance? PrefixTrie other)
             false)
        ))


  clojure.lang.ILookup
  (valAt [this key] nil)
  (valAt [this key notfound] nil)

  clojure.lang.Seqable
  (seq [this] (get-values this nil))

  clojure.lang.IPersistentCollection
  (count [this] (count (get-values this nil)))
  (cons [this other] (???))
  (equiv [this other] (identical? this other))

  clojure.lang.Associative
  (containsKey [this key] false)
  (entryAt [this key])
  (assoc [this key val]

    ;; return a new prefix trie
    )

  ;; dyna.IPrefixTrie
  ;; (true_arity [this] (count filter))





  ;; (get [this key] nil)
  ;; (set [this key value]
  ;;   ;; return a new prefix trie with this value added
  ;;   nil
  ;;   ))
  )

(defn make-prefixtrie [arity]
  (PrefixTrie. arity 0 nil nil))

(defn zip-tries [a b]
  nil ;; return some iterator over the two tries at the same time
  ;; tihs will need to
  )
