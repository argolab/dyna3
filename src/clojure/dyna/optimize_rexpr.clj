(ns dyna.optimize-rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.user-defined-terms :refer [user-rexpr-combined-no-memo]])
  (:require [clojure.set :refer [union]]))


;; operations which work best when there is a bit of a higher level
;; "perspective" on the R-expr compared to only using the rewrites directly

(defn optimize-aliased-variables
  ;; remove excess unify and project between variables which are unnecessary in the expression
  ([rexpr] (let [[unified-vars new-rexpr] (optimize-aliased-variables rexpr #{})]
             #_(when-not (= (exposed-variables rexpr) (exposed-variables new-rexpr))
               (debug-repl "not equal expose"))
             new-rexpr))
  ([rexpr proj-out-vars]
   (let [var-unifies (transient {})
         mr (cond
              (is-proj? rexpr)
              (let [pvar (:var rexpr)
                    prexpr (:body rexpr)
                    [nested-unifies nested-rexpr] (optimize-aliased-variables prexpr (conj proj-out-vars proj-out-vars)) ;; why are we passing the projected out var here, seems unnecessary?
                    self-var-unifies (disj (get nested-unifies pvar) pvar)  ;; if there is any other variable here
                    ret-rexpr (if-not (empty? self-var-unifies)
                                (let [new-variable (if (some is-constant? self-var-unifies)
                                                     (first (filter is-constant? self-var-unifies))
                                                     (first self-var-unifies))]
                                  (remap-variables nested-rexpr {pvar new-variable}))
                                (if (= nested-rexpr prexpr)
                                  rexpr ;; no change, so just return ourself
                                  (make-proj pvar nested-rexpr)))]
                (doseq [[k v] nested-unifies
                        :when (not= k pvar)]
                  (assoc! var-unifies k (union (get var-unifies k) (disj v pvar))))
                ;(dyna-assert (= (exposed-variables rexpr) (exposed-variables ret-rexpr)))
                ret-rexpr)

              (is-unify? rexpr) (let [[a b] (get-arguments rexpr)]
                                  (assoc! var-unifies a (conj (get var-unifies a #{}) b))
                                  (assoc! var-unifies b (conj (get var-unifies b #{}) a))
                                  rexpr) ;; there is no change to the expression here
              (is-disjunct? rexpr) rexpr ;; we do not evaluate disjunctions for variables which might get unified together
              :else ;; otherwise we should check all of the children of the expression to see if there is some structure
              (let [rr (rewrite-rexpr-children-no-simp rexpr
                                                       (fn [r]
                                                         (let [[unifies nr] (optimize-aliased-variables r proj-out-vars)]
                                                           (doseq [[k v] unifies]
                                                             (assoc! var-unifies k (union v (get var-unifies k))))
                                                           nr)))]
                rr))]
     [(persistent! var-unifies) mr])))

(defn optimize-lift-up-det-variables [rexpr]
  ;; variables which are determinstic from other variables which are set, should be lifted as high as possible in the context
  ;; this will allow for variables to get shared in multiple places without having to be aliased together
  ;; e.g.  (proj X (sum-agg (proj Y  (X=foo[Y])))) ===> (proj X (proj Y (X=foo[Y]) * (sum-agg ...)))
  (???)
  )

(defn optimize-redudant-constraints [rexpr]
  ;; calls to the same constraint should be optimized to only perform that call once
  )


(defn optimize-conjunct-of-disjuncts [rexpr]
  ;; there might be something which can only be optimized in the presence of
  ;; some subset of a disjunctive branch if we can eleminate those other
  ;; branches, then we might be able to identify that there is some branch which
  ;; we can entirely elminate from the program
  )

(defn optimize-refold-program [rexpr]
  ;; look for places where we might want to generate a new R-expr after we have expanded the program some depth
  ;; this might be useful in the case of recursive programs.
  )

#_(defn optimize-remove-unnecessary-nested-aggregators [rexpr]
  ;; the aggregator will get removed if there is only a single child in the
  ;; first place though if we are going to take the min of a min for example,
  ;; then we do not need to run two different aggregators.
  )

;; (defn- check-rexpr-basecases
;;   ([rexpr stack]
;;    (if )
;;    )
;;   ([rexpr] (recur rexpr ())))

;; (defn- get-all-conjunctive-rexprs [rexpr]
;;   ())


#_(defn optimize-disjuncts [rexpr]
  ;; look through the disjuncts and figure out if there are any branches which
  ;; are unnecessary of where extra constraints could be added to the branches.

  ;; if
  )
