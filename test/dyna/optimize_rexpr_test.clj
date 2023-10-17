#_(ns dyna.optimize-rexpr-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.rexpr :refer [simplify-top]])
  (:require [dyna.optimize-rexpr :refer [optimize-redudant-constraints]])
  (:require [dyna.utils :refer :all])
  (:require [dyna.simple-test :refer [str-test]]))

#_(deftest redudant-constraints
  (let [rexpr (make-conjunct [(make-lessthan (make-variable 'X) (make-variable 'Y) (make-variable 'Z1))
                              (make-lessthan (make-variable 'X) (make-variable 'Y) (make-variable 'Z2))])
        r2 (simplify-top rexpr)
        opt-r (optimize-redudant-constraints rexpr)]
    (is (= rexpr r2))
    (is (not= rexpr opt-r))
    (is (some is-unify? (map second (all-conjunctive-rexprs opt-r))))))
