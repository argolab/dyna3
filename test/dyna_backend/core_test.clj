(ns dyna-backend.core-test
  (:require [clojure.test :refer :all]
            [dyna-backend.core :refer :all]
            [dyna-backend.rexpr :refer :all]))

;; (deftest a-test
;;   (testing "FIXME, I fail."
;;     (is (= 0 1))))


(deftest basic-rexpr
  (let [rexpr (make-add 2 3 5)
        r2 (simplify rexpr)]
    (is (= r2 (make-multiplicity 1)))
    ))


;; (deftest basic-rexpr
;;   (let [expr '(if expression )])
;;   )
