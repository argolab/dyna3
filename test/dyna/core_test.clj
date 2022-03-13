(ns dyna.core-test
  (:require [clojure.test :refer :all]
            [dyna.core :refer :all]
            [dyna.base-protocols :refer :all]
            [dyna.rexpr :refer :all]
            [dyna.context :as context]
            [dyna.rexpr-builtins :refer :all]
            [dyna.utils :refer [debug-repl make-term match-term]]))


(deftest basic-rexpr
  (let [rexpr (make-add (make-constant 2) (make-constant 3) (make-constant 5))
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context ctx (simplify rexpr))
        r3 (make-multiplicity 1)]
    (is (= r2 r3))))


(deftest basic-rexpr2
  (let [rexpr (make-add (make-constant 2) (make-constant 3) (make-variable 'var1))
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify rexpr))
        r3 (make-multiplicity 1)]
        ;r3 (make-unify (make-variable 'var1) (make-constant 5))
    (is (= r2 r3))
    (is (= 5 (ctx-get-value ctx (make-variable 'var1))))
    (println ctx)))



(deftest basic-conjunct
  (let [rexpr (make-conjunct
                [(make-add (make-constant 2) (make-variable 'v1) (make-variable 'v2))
                 (make-add (make-constant 2) (make-constant 3) (make-variable 'v1))])
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))
        r3 (make-multiplicity 1)]
    (is (= r2 r3))
    (is (= (ctx-get-value ctx (make-variable 'v1)) 5))
    (is (= (ctx-get-value ctx (make-variable 'v2)) 7))))


(deftest basic-disjunct
  (let [rexpr (make-disjunct
               [(make-unify (make-variable 'foo) (make-constant 123))
                (make-unify (make-variable 'foo) (make-constant 123))])
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))
        r3 (make-multiplicity 2)]
    (is (= r2 r3))
    (is (= (ctx-get-value ctx (make-variable 'foo)) 123))))

(deftest basic-disjunct2
  ;; these can not be combined because the values of the variables are different
  (let [rexpr (make-disjunct
               [(make-unify (make-variable 'foo) (make-constant 123))
                (make-unify (make-variable 'foo) (make-constant 456))])
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))]
    (is (= rexpr r2))
    (is (not (is-bound-in-context? (make-variable 'foo) ctx)))))

(deftest basic-aggregator1
  (let [rexpr (make-aggregator "+="
                               (make-variable 'out)
                               (make-variable 'agg-in)
                               true
                               (make-unify (make-variable 'agg-in) (make-constant 777)))
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))]
    (is (= (make-multiplicity 1) r2))
    (is (= (ctx-get-value ctx (make-variable 'out)) 777))))

(deftest basic-aggregator2
  (let [rexpr (make-aggregator "+="
                               (make-variable 'out)
                               (make-variable 'agg-in)
                               true
                               (make-conjunct [(make-multiplicity 2)
                                               (make-unify (make-variable 'agg-in)
                                                           (make-constant 333))]))
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))]
    (is (= (make-multiplicity 1) r2))
    (is (= (ctx-get-value ctx (make-variable 'out)) 666))))

(deftest basic-aggregator3
  (let [rexpr (make-aggregator "+="
                               (make-variable 'out)
                               (make-variable 'agg-in)
                               true
                               (make-disjunct
                                [(make-unify (make-variable 'agg-in) (make-constant 111))
                                 (make-unify (make-variable 'agg-in) (make-constant 666))]))
        ctx (context/make-empty-context rexpr)
        r2 (context/bind-context-raw ctx (simplify-fully rexpr))]
    (is (= (make-multiplicity 1) r2))
    (is (= (ctx-get-value ctx (make-variable 'out)) 777))))


(deftest make-match-term
  (let [term (make-term ("myterm" ("another" 1 2 3)))
        cnt (atom 0)]
    (dyna.utils/match-term term ("myterm" ("another" a b c))
                           (assert (= a 1))
                           (swap! cnt inc))
    (assert (= 1 @cnt))))


(deftest match-rexpr-test
  (let [rexpr (make-unify (make-variable 'a) (make-variable 'b))
        cnt (atom 0)]
    (match-rexpr rexpr (unify (:variable avar) (:variable bvar))
                 (swap! cnt inc)
                 (assert (= avar (make-variable 'a))))

    (assert (= @cnt 1))))
