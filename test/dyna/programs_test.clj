(ns dyna.programs-test
  (:require [clojure.test :refer :all]
            [clojure.java.io :refer [as-file as-relative-path]]
            [dyna.core]
            [dyna.system :refer [make-new-dyna-system run-under-system]]
            [dyna.ast-to-rexpr :refer [import-file-url]]
            [dyna.utils :refer [debug-repl]])
  (:import [dyna DynaUserAssert]))


(def test-dir (as-file "./test_programs"))
;;(debug-repl)


(defmacro make-file-test [fname]
  `(deftest ~(symbol fname)
     (let [sstate# (make-new-dyna-system)]
       (try
         (run-under-system sstate#
                           (import-file-url (.toURL (as-file (str "./test_programs/" ~fname ".dyna")))))
         (is true)
         (catch DynaUserAssert e#
           (is false)
           (throw e#))))))


(make-file-test "basic1")
(make-file-test "edit_distance")
(make-file-test "quicksort")
(make-file-test "simple_matrix")

(comment
  (eval `(do
           ~@(for [f (file-seq test-dir)]
               (let [name (.getName f)]
                 (when (and (.isFile f) (.endsWith name ".dyna"))
                   (let [fname (.substring name 0 (- (.length name) 5))]
                     `(make-file-test ~fname))))))))
