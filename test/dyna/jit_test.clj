(ns dyna.jit-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.rexpr :refer [simplify]])
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.rexpr-jit :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.context :as context]))


#_(deftest basic-jit
  (let [rexpr (make-unify (make-variable 'a) (make-variable 'b))
        rr (get-rexpr-arg-map rexpr)]
                                        ; (debug-repl)
    ))

(deftest basic-jit2
  (let [rexpr (make-conjunct [(make-add (make-variable 'a) (make-variable 'b) (make-variable 'c))
                              (make-times (make-variable 'c) (make-constant 7) (make-variable 'd))])
        [synth-rexpr _](synthize-rexpr rexpr)]
    (is (not (nil? synth-rexpr)))))

(deftest basic-jit3
  (let [rexpr (make-proj (make-variable 'c)  ;; d = (a + 1)*7
                         (make-conjunct [(make-add (make-variable 'a) (make-constant 1) (make-variable 'c))
                                         (make-times (make-variable 'c) (make-constant 7) (make-variable 'd))]))
        [jit-rexpr jit-type] (synthize-rexpr rexpr)]
    ;; make a new rewrite rule
    (synthize-rewrite-rule jit-rexpr
                           :arg-matches {(make-variable 'a) [:ground]
                                         (make-variable 'd) [:free]} ;; a list of which pattern matches should be considered as matching
                           :example-values {;(make-variable 'a)  22  ;; an "example" value which can be used to generate code for the rewrite, but not to condition specifically on this value
                                            }
                           :values {;(make-variable 'a) 22  ;; make a rewrite which is _specific_ to this particular value
                                    })

    (let [rr (make-conjunct [(make-unify (make-variable 'a) (make-constant 11))
                             jit-rexpr])
          ctx (context/make-empty-context rr)
          res (context/bind-context-raw ctx (simplify rr))]
      ;(debug-repl "res from jit") ;; this should have that the
      (is (= res (make-multiplicity 1)))
      (is (= (ctx-get-value ctx (make-variable 'd)) (* (+ 11 1) 7))))))
