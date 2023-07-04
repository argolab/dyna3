(ns dyna.programs-test
  (:require [dyna.core])
  (:require [dyna.simple-test :refer [str-test]])
  (:require [clojure.test :refer :all])
  (:require [clojure.java.io :refer [as-file as-relative-path]])
  (:require [dyna.system :refer [make-new-dyna-system run-under-system]])
  (:require [dyna.ast-to-rexpr :refer [import-file-url]])
  ;(:require [dyna.utils :refer [debug-repl]])
  (:import [dyna DynaUserAssert]))


(def test-dir (as-file "./test_programs"))
;;(debug-repl)

(defn run-file [fname]
  (let [sstate (make-new-dyna-system)]
    (try
      (run-under-system sstate
                        (import-file-url (.toURL (as-file (str "./test_programs/" fname ".dyna")))))
      (is true)
      (catch DynaUserAssert e
        (is false)
        (throw e)))))

(deftest dummy) ;; for intellij

(defmacro make-file-test [fname]
  `(deftest ~(symbol fname)
     (run-file ~(str fname))))

(make-file-test "basic1")
(make-file-test "edit_distance")
(make-file-test "quicksort")
(make-file-test "simple_matrix")
(make-file-test "import_file")
(make-file-test "parser_generator_test")
(make-file-test "cky_parsing2")


;; for some reason, attempting to do file io in the macro causes the loading of other unrelated stuff to not work
;; think this is probably some issue inside of the clojure compiler
(comment
  (print `(do
            (print "did eval of files")
            ~@(for [f (file-seq test-dir)]
                (let [name (.getName f)]
                  (comment (when (and (.isFile f) (.endsWith name ".dyna"))
                             (let [fname (.substring name 0 (- (.length name) 5))]
                                        ;`(make-file-test ~(str fname))
                               )))))))

  (defmacro get-file-tests []
    (let [fd (java.io.File. "./test_programs")
          names (.list fd)]
      `(do ~@(for [name names]
               (when (.endsWith name ".dyna")
                 (let [fname (.substring name 0 (- (.length name) 5))]
                   `(make-file-test ~fname))))))))

;(get-file-tests)


;; (let [fd (java.io.File. "./test_programs")
;;       fn (.list fd)]
;;   (eval `(do ~@(for [f fn]
;;                  (when (.endsWith f ".dyna")
;;                    `(make-file-test f))))))

;; (doseq [f (file-seq test-dir)]
;;   (Thread/sleep 5))

;; (doseq [f (file-seq test-dir)]
;;   (print f))
