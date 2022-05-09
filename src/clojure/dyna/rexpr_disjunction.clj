(ns dyna.rexpr-disjunction
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.prefix-trie :refer :all])
  (:require [clojure.set :refer [subset?]]))

(assert false)  ;; this file is not used yet

(def ^:dynamic *disjunct-op-remove-if-single* true)

(def ^:dynamic *disjunct-constructed-add-function* nil)

;; the prefix trie will have that


;; more efficient implementations of disjunction which can handle special (but
;; common) cases.  This can include dispatching on the values of variables
;; directly to a branch, like a trie.  We should be able to construct these
;; versions of a disjunction from the generic version of a disjunction that is
;; defined in rexpr.clj



;; multiple levels of matching variables should also be a thing that was
;; integrated into the aggregator before, or the disjunction included that it
;; was matching the expression

;; (defn- recurse-values-depth [m depth]
;;   (if (= depth 0)
;;     (vals m)
;;     (lazy-seq (map #(recurse-values-depth % (- depth 1)) (vals m)))))


;; I suppose that in the case that there are non-ground disjunction-variables, then this would still need this structure
;; once all of the disjunct variables are ground, then this can just rewrite as the wrapped R-expr.  I suppose that this can
;; also consider which of the variables are forced to take a particular value.  Then those can be created as unification expressions
;; such that it will take which of the values might corresponds with it having some of the different
(def-base-rexpr disjunct-op [:var-list disjunction-variables
                             ;:disjunct-trie rexprs
                             :prefix-trie rexprs
                             ]
  ;; (primitive-rexpr [this] (assert false))
  ;; (get-children [this] (assert false))
  ;; (primitive-rexpr [this] ;; this would have to construct many disjuncts for the given expression.
  ;;                  )

  ;; this will need to walk through all of the rexprs trie and find the depth in
  ;; which an expression corresponds with it.  I suppose that we do not need to
  ;; have a list of disjuncts, as those can just be other disjunctive R-exprs in
  ;; the case that there is more than 1 thing
  (get-children [this] (map second (get-values rexprs)))


  (remap-variables
   [this variable-renaming-map]
   (if (empty? variable-renaming-map) this
       (let [new-disjuncts (map #(get variable-renaming-map % %) disjunction-variables)]
         ;; if one of the variables is a constant, then we can avoid keeping the entire structure
         ;; also we might want to have some of the expressions

         (assert false)
         )
       )
   )

  )

(def-rewrite
  :match (disjunct-op var-list rexprs)
  :run-at :construction
  :is-check-rewrite true
  (let [query-key (map get-value var-list)]
    (when-not (every? (fn [x] (and (rexpr? x)
                                   ;; the variables which are exposed should be a subset of what is not ground
                                   ;; or are we going to have to represent which of the values are represented with
                                   (subset? (exposed-variables x) var-list)))
                      (map second (get-values rexprs query-key)))
      (debug-repl "failed to have rexpr in trie")
      (???))))

(def ^:private not-seen-in-trie (Object.))

;; there can be a function which is called whenever a new disjunct is constructed

(def-rewrite
  :match (disjunct-op var-list rexprs)
  :run-at [:standard :inference]
  ;; if there is only a single value then it should just return that entry
  (let [values-seen (transient (vec (repeat (count var-list) not-seen-in-trie)))
        query-key (map get-value var-list)
        new-trie (volatile! (make-prefixtrie (count var-list)))

        new-trie (map-trie rexprs query-key (fn [key val]
                                              ;; this might result in new variables getting bound
                                              ;; but if there is some value which does not have

                                              ))
        ]
    (doseq [[key val] (get-values trie query-key)]
      ;; this is going to identify which of the values are in the keys, and then
      (let [disj-ctx (context/make-nested-context-disjunct val)
            new-rexpr (context/bind-context-raw)]
        )

      )
    )
  )


(def-rewrite
  :match {:rexpr (disjunct (:rexpr-list children))
          :check (not (nil? *disjunct-constructed-add-function*))}
  :run-at :construction
  ;; this would identify that there is some disjunct which is constructed, and
  ;; then it can added it to the top level though if there is an aggregator
  ;; which is also getting rewritten, then it would have to unbind the variable
  ;; the context should really be the thing which is tracking the operation
  ;; (rather than a dynamic variable)
  )
