(ns dyna.core-test
  (:require [clojure.test :refer :all]
            [dyna.core :refer :all]
            [dyna.base-protocols :refer :all]
            [dyna.rexpr :refer :all]
            [dyna.context :as context]
            [dyna.system :as system]
            [dyna.rexpr-builtins :refer :all]
            [dyna.utils :refer [debug-repl make-term match-term defsimpleinterface]]))


(defmacro run-unoptimized-rexprs [& body]
  `(try
     (do
       (alter-var-root #'system/use-optimized-rexprs (constantly false))
       ~@body)
     (finally
       (alter-var-root #'system/use-optimized-rexprs (constantly true)))))

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
  (run-unoptimized-rexprs
    (let [rexpr (make-disjunct
                 [(make-unify (make-variable 'foo) (make-constant 123))
                  (make-unify (make-variable 'foo) (make-constant 123))])
          ctx (context/make-empty-context rexpr)
          r2 (context/bind-context-raw ctx (simplify-fully rexpr))
          r3 (make-multiplicity 2)]
      (is (= r2 r3))
      (is (= (ctx-get-value ctx (make-variable 'foo)) 123)))))

(deftest basic-disjunct2
  ;; these can not be combined because the values of the variables are different
  (run-unoptimized-rexprs  ;; the disjunct will get replaced with the optimized disjunct if this is set to true (the default)
    (let [rexpr (make-disjunct
                 [(make-unify (make-variable 'foo) (make-constant 123))
                  (make-unify (make-variable 'foo) (make-constant 456))])
          ctx (context/make-empty-context rexpr)
          r2 (context/bind-context-raw ctx (simplify-fully rexpr))]
      (is (= rexpr r2))
      (is (not (is-bound-in-context? (make-variable 'foo) ctx))))))

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
  (run-unoptimized-rexprs
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
      (is (= (ctx-get-value ctx (make-variable 'out)) 777)))))


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

    (is (= @cnt 1))))


(defsimpleinterface my-simple-interface
  (my-simple-interface-fn1 [a b c])
  (my-simple-interface-fn2 [a d]))

(deftype my-simple-type [v]
    my-simple-interface
  (my-simple-interface-fn1 [this a b c]
    (+ a (* b 5) (* c 7)))
  (my-simple-interface-fn2 [this a d]
    (+ a (* d 5) (* v 7))))

(deftest simple-interface
  (let [val (my-simple-type. 17)
        r1 (my-simple-interface-fn1 val 3 11 13)
        r2 (my-simple-interface-fn2 val 3 11)]
    (is (= r1 (+ 3 (* 11 5) (* 13 7))))
    (is (= r2 (+ 3 (* 11 5) (* 17 7))))))


(def-base-rexpr no-arg-test-case [])
