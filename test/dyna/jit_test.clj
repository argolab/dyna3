(ns dyna.jit-test
    (:require [clojure.test :refer :all])
    (:require [dyna.core])
    (:require [dyna.rexpr :refer [simplify simplify-fully]])
    (:require [dyna.utils :refer :all])
    (:require [dyna.rexpr-constructors :refer :all])
    (:require [dyna.rexpr-jit-v2 :refer :all])
    (:require [dyna.base-protocols :refer :all])
    (:require [dyna.context :as context])
    (:require [dyna.system :refer [*generate-new-jit-rewrites*]]))

(deftest basic-jit1
  ;; test just creating the synthized R-expr
  (let [rexpr (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                              (make-times (make-variable 'c) (make-constant 7) (make-variable 'd))])
        [synth-rexpr _](synthize-rexpr rexpr)
        prim-r (primitive-rexpr synth-rexpr)]
    (is (not (nil? synth-rexpr)))
    (is (-> synth-rexpr type .getSimpleName (.startsWith "jit-rexpr")))
    (is (= prim-r rexpr))))


(deftest basic-jit2
  ;; (a + b)*7 = d
  ;; test creating a basic rewrite where all variables are exposed
  (let [rexpr (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                              (make-times (make-variable 'c) (make-constant 7) (make-variable 'd))])
        [synth-rexpr _](synthize-rexpr rexpr)]
    (is (-> synth-rexpr type .getSimpleName (.startsWith "jit-rexpr")))
    (let [ctx (context/make-empty-context synth-rexpr)]
      (ctx-set-value! ctx (make-variable 'a) 3)
      (ctx-set-value! ctx (make-variable 'b) 2)
      (binding [*generate-new-jit-rewrites* false]
        (let [res (context/bind-context-raw ctx (simplify-fully synth-rexpr))]
          (is (identical? res synth-rexpr))))
      (binding [*generate-new-jit-rewrites* true]
        (let [res (context/bind-context-raw ctx (simplify-fully synth-rexpr))]
          (is (= (make-multiplicity 1) res))
          (is (= 35 (ctx-get-value ctx (make-variable 'd)))))))))

(deftest basic-jit3
  ;; test creating internal variables which are projected out of the expression
  (let [rexpr (make-proj (make-variable 'c)  ;; d = (a + 1)*7
                         (make-conjunct [(make-add (make-variable 'a) (make-constant 1) (make-variable 'c))
                                         (make-times (make-variable 'c) (make-constant 7) (make-variable 'd))]))
        [synth-rexpr jit-type] (synthize-rexpr rexpr)]
    (is (-> synth-rexpr type .getSimpleName (.startsWith "jit-rexpr")))

    (let [ctx (context/make-empty-context synth-rexpr)]
      (ctx-set-value! ctx (make-variable 'a) 3)
      (binding [*generate-new-jit-rewrites* true]
        (let [res (context/bind-context-raw ctx (simplify-fully synth-rexpr))]
          (is (= (make-multiplicity 1) res))
          (is (= 28 (ctx-get-value ctx (make-variable 'd)))))))))

(deftest basic-jit4
  ;; test having an incomplete computation, where an existing rewrite will get aborted part way through because of a partial match
  (let [rexpr (make-proj-many [(make-variable 'c) (make-variable 'e)]
                                ;; a + b + d + f = g
                                (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                                                (make-add (make-variable 'c) (make-variable 'd) (make-variable 'e))
                                                (make-add (make-variable 'e) (make-variable 'f) (make-variable 'g))]))
        [synth-rexpr jit-type] (synthize-rexpr rexpr)
        rr (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                           (make-unify (make-variable 'b) (make-constant 2))
                           (make-unify (make-variable 'd) (make-constant 3))
                           synth-rexpr])
        rr2 (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                            (make-unify (make-variable 'b) (make-constant 2))
                            synth-rexpr])
        rr3 (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                            (make-unify (make-variable 'b) (make-constant 2))
                            (make-unify (make-variable 'f) (make-constant 10))
                            (make-unify (make-variable 'g) (make-constant 12))
                            synth-rexpr])
        ctx (context/make-empty-context rr)
        ctx2 (context/make-empty-context rr2)
        ctx3 (context/make-empty-context rr3)]
    (binding [*generate-new-jit-rewrites* true]
      (let [res (context/bind-context-raw ctx (simplify-fully rr))]
        (is (is-add? res))
        (is (= (make-constant 6) (:v0 res))))
      (let [res2 (context/bind-context-raw ctx2 (simplify-fully rr2))]
        (is (not= res2 rr2))
        (is (some #{(make-constant 3)} (get-arguments res2))) ;; the constant 3 should appear somewhere in the parameters which are returned as it already did one addition
        )
      (let [res3 (context/bind-context-raw ctx3 (simplify-fully rr3))]
        (is (is-multiplicity? res3))))))

(deftest basic-jit5
  (let [rexpr (make-conjunct [(make-lessthan (make-variable 'a) (make-variable 'b) (make-constant true))
                              (make-lessthan (make-variable 'b) (make-variable 'c) (make-constant true))])
        [synth-rexpr jit-type] (synthize-rexpr rexpr)
        rr (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                           (make-unify (make-variable 'b) (make-constant 2))
                           synth-rexpr])
        rr2 (make-conjunct [(make-unify (make-variable 'a) (make-constant 10))
                            (make-unify (make-variable 'c) (make-constant 1))
                            synth-rexpr])
        ctx (context/make-empty-context rr)
        ctx2 (context/make-empty-context rr2)]
    (binding [*generate-new-jit-rewrites* true]
      (let [res2 (context/bind-context-raw ctx2 (simplify-fully rr2))]
        ;; this needs to do inference constraints to identify a new constraint between a and cand then that constraint should fail as a result
        (is (is-empty-rexpr? res2))))))

#_(deftest basic-jit6
  ;; test constructing an R-expr with holes.  This will mean that it should
  ;; still call simplify on the holed expression we are also going to want to
  ;; allow for the hole expression to get embedded into the current R-expr.  How
  ;; it would allow for it to find something
  (let [rexpr (make-conjunct
               (make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
               )] )

  )

;; Done:
;; - inference against other parts of the R-expr


;; TODO:
;;  - holes of other R-exprs
;;  - iterators
;;    - aggregators/disjunction?
;;  - inference (against outside context)
;;
;;  - converting R-exprs into the synth form
;;     - matching against already existing synth forms
;;     - heuristics for converting user defined functors into synth forms
;;     -

;; It should be able to do inference rewrites internal to the JITted R-expr.
;; The inference would only apply in the case that it has to look outside of the expressions

(comment

  #_(deftest basic-jit
      (let [rexpr (make-unify (make-variable 'a) (make-variable 'b))
            rr (get-rexpr-arg-map rexpr)]
                                        ; (debug-repl)
        ))





  (deftest basic-jit4
    (let [rexpr (make-proj-many [(make-variable 'c) (make-variable 'e)]
                                ;; a + b + d + f = g
                                (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                                                (make-add (make-variable 'c) (make-variable 'd) (make-variable 'e))
                                                (make-add (make-variable 'e) (make-variable 'f) (make-variable 'g))]))
          [jit-rexpr jit-type] (synthize-rexpr rexpr)]
      (synthize-rewrite-rule jit-rexpr
                             :arg-matches {(make-variable 'a) [:ground]
                                           (make-variable 'b) [:ground]
                                           (make-variable 'd) [:ground]
                                           (make-variable 'f) [:free]
                                           (make-variable 'g) [:free]})
      (let [rr (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                               (make-unify (make-variable 'b) (make-constant 2))
                               (make-unify (make-variable 'd) (make-constant 3))
                               jit-rexpr])
            ctx (context/make-empty-context rr)
            res (context/bind-context-raw ctx (simplify rr))]
                                        ;(debug-repl "res from jit")
        (is (= (make-add (make-constant 6) (make-variable 'f) (make-variable 'g)) res)))))

  (deftest basic-jit5
    (let [rexpr (make-proj-many [(make-variable 'c) (make-variable 'e)]
                                ;; a + b + d + f = g
                                (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                                                (make-add (make-variable 'c) (make-variable 'd) (make-variable 'e))
                                                (make-add (make-variable 'e) (make-variable 'f) (make-variable 'g))]))
          [jit-rexpr jit-type] (synthize-rexpr rexpr)]
      (synthize-rewrite-rule jit-rexpr
                             :arg-matches {(make-variable 'a) [:ground]
                                           (make-variable 'b) [:ground]
                                           (make-variable 'd) [:free]
                                           (make-variable 'f) [:free]
                                           (make-variable 'g) [:free]})
      (let [rr (make-conjunct [(make-unify (make-variable 'a) (make-constant 1))
                               (make-unify (make-variable 'b) (make-constant 2))
                               jit-rexpr])
            ctx (context/make-empty-context rr)
            res (context/bind-context-raw ctx (simplify rr))]
                                        ;(debug-repl "res from jit")
        (is (some #{(make-constant 3)} (get-arguments res))) ;; check one of the arguments represents the result of the computation
        (is (.startsWith (str (rexpr-name res)) "jit-rexpr")))))
  )
