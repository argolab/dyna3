(ns dyna-backend.parser-test
  (:require [clojure.test :refer :all])
  (:require [dyna-backend.parser_interface :refer [parse-string]]))

(deftest basic-parser
  (parse-string "foo1 = 123."))
