(ns dyna.rexpr-disjunction
  (:require [dyna.rexpr :refer :all]))

;; more efficient implementations of disjunction which can handle special (but
;; common) cases.  This can include dispatching on the values of variables
;; directly to a branch, like a trie.  We should be able to construct these
;; versions of a disjunction from the generic version of a disjunction that is
;; defined in rexpr.clj



;; multiple levels of matching variables should also be a thing that was
;; integrated into the aggregator before, or the disjunction included that it
;; was matching the expression

(defn- recurse-values-depth [m depth]
  (if (= depth 0)
    (vals m)
    (lazy-seq (map #(recurse-values-depth % (- depth 1)) (vals m)))))


;; I suppose that in the case that there are non-ground disjunction-variables, then this would still need this structure
;; once all of the disjunct variables are ground, then this can just rewrite as the wrapped R-expr.  I suppose that this can
;; also consider which of the variables are forced to take a particular value.  Then those can be created as unification expressions
;; such that it will take which of the values might corresponds with it having some of the different
(def-base-rexpr disjunct-op [:var-list disjunction-variables
                             ;:disjunct-trie rexprs
                             :unchecked rexprs
                             ]
  ;; (primitive-rexpr [this] (assert false))
  ;; (get-children [this] (assert false))
  ;; (primitive-rexpr [this] ;; this would have to construct many disjuncts for the given expression.
  ;;                  )

  ;; this will need to walk through all of the rexprs trie and find the depth in
  ;; which an expression corresponds with it.  I suppose that we do not need to
  ;; have a list of disjuncts, as those can just be other disjunctive R-exprs in
  ;; the case that there is more than 1 thing
  (get-children [this] (recurse-values-depth rexprs (count disjunction-variables)))

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
