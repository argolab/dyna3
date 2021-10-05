(ns dyna-backend.prefix-trie
  (:import [dyna_backend IPrefixTrie]))


;; (gen-interface
;;  :name dyna_backend.IPrefixTrie
;;  :extends [clojure.lang.ILookup]
;;  :methods [[get [Object] Object]
;;            [set [Object Object] "Ldyna_backend.IPrefixTrie;"]
;;            ])


(deftype PrefixTrie [^int arity
                     filter
                     root]
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
  (seq [this] nil)

  clojure.lang.IPersistentCollection
  (count [this] 0)
  (cons [this other] nil)
  (equiv [this other] (identical? this other))

  clojure.lang.Associative
  (containsKey [this key] false)
  (entryAt [this key] nil)
  (assoc [this key val]
    ;; return a new prefix trie
    )

  ;; dyna_backend.IPrefixTrie
  ;; (true_arity [this] (count filter))





  ;; (get [this key] nil)
  ;; (set [this key value]
  ;;   ;; return a new prefix trie with this value added
  ;;   nil
  ;;   ))
  )

(defn make-prefixtrie [arity]
  (PrefixTrie. arity (repeat arity nil) nil))

(defn zip-tries [a b]
  nil ;; return some iterator over the two tries at the same time
  ;; tihs will need to
  )
