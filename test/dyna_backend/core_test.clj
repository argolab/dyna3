(ns dyna-backend.core-test
  (:require [clojure.test :refer :all]
            [dyna-backend.core :refer :all]
            [dyna-backend.rexpr :refer :all]))

;; (deftest a-test
;;   (testing "FIXME, I fail."
;;     (is (= 0 1))))


(deftest basic-rexpr
  (let [rexpr (make-add (make-constant 2) (make-constant 3) (make-constant 5))
        r2 (simplify rexpr)
        r3 (make-multiplicity 1)]
    (is (= r2 r3))
    ))


;; (deftest basic-rexpr
;;   (let [expr '(if expression )])
;;   )
