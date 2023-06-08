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
        ctx (context/make-empty-context rr)
        ctx2 (context/make-empty-context rr2)]
    (binding [*generate-new-jit-rewrites* true]
      (let [res (context/bind-context-raw ctx (simplify-fully rr))]
        (is (is-add? res))
        (is (= (make-constant 6) (:v0 res))))
      (let [res2 (context/bind-context-raw ctx2 (simplify-fully rr2))]
        (is (not= res2 rr2))
        (debug-repl "aborted rewrite part way"))
      )))

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
