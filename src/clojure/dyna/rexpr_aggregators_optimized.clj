(ns dyna.rexpr-aggregators-optimized
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexprs :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.rexpr-aggregators :refer [aggregators]])
  (:import [dyna.rexprs proj-rexpr disjunct-rexpr])
  (:import [dyna.rexpr-disjunction disjunct-op-rexpr]))

(def-base-rexpr aggregator-op-outer [:unchecked operator
                                     :var result
                                     :rexpr bodies])

(def-base-rexpr aggregator-op-inner [:hidden-var incoming
                                     :var-list projected ;; all of these variables are hidden
                                     :rexpr body]
  (exposed-variables [this]
                     (catch-field cached-exposed-variables
                                  (difference (exposed-variables body)
                                              (into #{incoming} projected))))
  (remap-variables [this variable-map]
                   ;; this is going to have to perform remapping of the body, and the body is going t
                   (???))

  (remap-variables-handle-hidden [this variable-map]
                                 (???)))


(def-rewrite
  :match {:rexpr (aggregator (:unchecked operator) (:any result-variable) (:any incoming-variable)
                             (#(= % true) body-is-conjunctive) (:rexpr R))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (make-aggregator-op-outer (get @aggregators operator) result-variable
                            (make-aggregator-op-inner incoming-variable
                                                      []
                                                      R)))

;; if there is a project nested inside of the aggregator inner expression, then we are going pull the projection out and add it to the aggregator
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:var-list projected-vars) (proj (:variable hid-var) (:rexpr R)))
          :check (and system/*use-optimized-rexprs*
                      (not (some #(= % hid-var) projected-vars)))}
  :run-at :construction
  (make-aggregator-op-inner incoming (conj projected-vars hid-var) R))

;; we want to lift the disjunction out of the aggregation, as we can handle the disjunctions before there are
(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:any-list projected-vars) (disjunct (:rexpr-list Rs)))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (make-disjunct (vec (map #(make-aggregator-op-inner incoming projected-vars %) Rs))))

(def-rewrite
  :match {:rexpr (aggregator-op-inner (:any incoming) (:any-list projected-vars) (disjunct-op (:any-list disjunction-variables) (:unchecked trie-Rs)))
          :check system/*use-optimized-rexprs*}
  :run-at :construction
  (do
    (debug-repl "optimized aggregator disjunction trie")
    (???)))

(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr Rbody))
  :run-at [:standard :inference]
  (do (if (is-disjunct-op? Rbody)
        ;; then this can have a more optimized implementation when running through
        )

      (let [all-args-ground (every? is-ground? (exposed-variables Rbody))]
        ;; this is going to have to

        ;; then the variable which

        )))

;; in the case that the disjunct is lifted out, it would be possible that
;; something which does not contain the proejcted vars and does not contain the
;; incoming-variables is also going to be lifted out.  Which means that this is
;; not able to just perform "sideways" passing of the information
(def-rewrite
  :match (aggregator-op-inner (:any incoming-variable) (:any-list projected-vars) (:rexpr Rbody))
  :run-at [:standard :inference]
  (let [ctx (context/make-nested-context-proj Rbody (conj projected-vars incoming-variable))
        nR (context/bind-context ctx (simplify Rbody))]

    ;; for every variable in the context which is bound and projected, we are
    ;; going to have to remap the variable to remove it

    (if (is-empty-rexpr? nR) ;; if there is nothing in the result, then this entire branch is going to map to zero
      (make-multiplicity 0)

      (let [new-incoming (if (is-bound-in-context? incoming-variable ctx)
                           (make-constant (get-value-in-context incoming-variable ctx))
                           incoming-variable)
            remapping-map (merge (into {} (remove nil?
                                                  (map (fn [v] (if (is-bound-in-context? v ctx)
                                                                 [v (make-constant (get-value-in-context v ctx))]))
                                                       projected-vars)))
                                 (if (is-bound-in-context? incoming-variable ctx)
                                   {incoming-variable new-incoming}))
            new-projected (vec (filter #(not (is-bound-in-context? %)) projected-vars))
            replaced-R (remap-variables nR remapping-map)]
        (make-aggregator-op-inner new-incoming new-projected replaced-R)))))

;; these are only conjunctive, so if the body is zero, then the expression will also be zero
(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result) (is-empty-rexpr? _))
  :run-at [:standard :construction]
  (make-multiplicity 0))
