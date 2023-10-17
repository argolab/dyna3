(ns dyna.optimize-rexpr
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.user-defined-terms :refer [user-rexpr-combined-no-memo]])
  (:require [clojure.set :refer [union intersection]])
  (:import [java.util IdentityHashMap]))


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

(defrecord redudant-constraint-var [id])
(defn- redudant-constraints [parent-replace-map rexpr]
  (let [conj-rexpr (all-conjunctive-rexprs rexpr)
        det-var-map (group-by :rexpr-remapped
                               (for [[projected-vars cr] conj-rexpr
                                     :when (and (not (is-conjunct? cr)) (is-constraint? cr))
                                     :let [vd (variable-functional-dependencies cr)]
                                     [ground-vars free-vars] vd]
                                 (let [i (volatile! 0)
                                       m (volatile! {})
                                       remapped (remap-variables-func cr (fn [v]
                                                                           (if (contains? free-vars v)
                                                                             (let [g (make-variable (redudant-constraint-var. (vswap! i inc)))]
                                                                               (vswap! m assoc g v)
                                                                               g)
                                                                             v)))]
                                   {:projected-vars projected-vars
                                    :rexpr cr
                                    :require-ground ground-vars
                                    :free-vars free-vars
                                    :rexpr-remapped remapped
                                    :remap @m})))
        replace-map (merge (into {} (for [[group-key all-constraints] det-var-map
                                          :let [possible-picks (remove (fn [x] (not (empty? (intersection (:projected-vars x) (:free-vars x)))))
                                                                       all-constraints)]
                                          :when (not (empty? possible-picks))]
                                      [group-key (first possible-picks)]))
                           parent-replace-map ;; let the parent replace map work as an override so that if something already exists, we can still call it
                           )
        ^IdentityHashMap replace-rexprs (IdentityHashMap.)]
    (doseq [[group-key all-constraints] det-var-map
            :let [pick (get replace-map group-key)]
            :when (not (nil? pick))
            to-replace (remove (partial identical? pick) all-constraints)]
      (assert (= (set (keys (:remap pick))) (set (keys (:remap to-replace)))))
      (.put replace-rexprs
            (:rexpr to-replace)
            (make-conjunct (vec (for [k (keys (:remap pick))]
                                  (make-no-simp-unify (strict-get (:remap pick) k)
                                                      (strict-get (:remap to-replace) k)))))))
    (letfn [(remap-fn [r]
              (let [z (.get replace-rexprs r)]
                (cond (not (nil? z)) z

                      (is-disjunct? r) (rewrite-rexpr-children r (partial redudant-constraints replace-map))

                      (is-disjunct-op? r) r

                      :else (rewrite-rexpr-children r remap-fn))))]
      (remap-fn rexpr))))

(defn optimize-redudant-constraints [rexpr]
  (redudant-constraints {} rexpr))


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
