(ns dyna-backend.parser-test
  (:require [clojure.test :refer :all])
  (:require [dyna-backend.parser_interface :refer [parse-string]]))

(deftest basic-parser
  (parse-string "foo1 = 123."))

(deftest dynabase-test
  (parse-string "db_baz(X) = Y = 9, { something(W) = W*44. }."))
