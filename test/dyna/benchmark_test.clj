(ns dyna.benchmark-test
  (:require [clojure.test :refer :all])
  (:require [dyna.core])
  (:require [dyna.rexpr :refer [simplify simplify-fully null-term simplify-top find-iterators]])
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr-constructors :refer :all])
  (:require [dyna.rexpr-jit-v2 :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.context :as context])
  (:require [dyna.system :as system])
  (:require [clojure.data.csv :as csv])
  (:require [clojure.java.io :as io])
  (:require [clojure.string :as string])
  (:import [dyna StatusCounters]))

(defn- synthize-rexpr [r]
  (tbinding [generate-new-jit-states true]
            (convert-to-jitted-rexpr r)))


(def benchmark-rexpr
  ;; this is equivalent to f(X) += N:range(0,X).
  (make-aggregator "+=" (make-variable "result") (make-variable "incoming") true (make-range (make-constant 0)
                                                                                             (make-variable "X")
                                                                                             (make-constant 1)
                                                                                             (make-variable "incoming")
                                                                                             (make-constant true))))

(defn f-clojure [X]
  (reduce + (range X)))

(defn f-closed-form [X]
  (/ (* (- X 1) X) 2))

(defn run-benchmark [func]
  (for [N (range 10 10000)] ;; make this count by 10?
    (do (println N)
        (let [start-matches-attempted (StatusCounters/get_matches_attempted)
              start-rewrites-performed (StatusCounters/get_rewrites_performed)
              start-rexpr-created (StatusCounters/get_rexpr_created)
              start (. System nanoTime)]
          (dotimes [i 10]
            (func N))
          (let [end (. System nanoTime)]
            [N (- end start)
             (- (StatusCounters/get_matches_attempted) start-matches-attempted)
             (- (StatusCounters/get_rewrites_performed) start-rewrites-performed)
             (- (StatusCounters/get_rexpr_created) start-rexpr-created)
             ])))))

(deftest basic-rewrite-bench
  (let [rexpr benchmark-rexpr
        br (run-benchmark
            (fn [to-value]
              (let [ctx (context/make-empty-context rexpr)]
                (ctx-set-value! ctx (make-variable "X") to-value)
                (context/bind-context-raw
                 ctx
                 (let [res (simplify-fully rexpr)]
                   (is (= res (make-multiplicity 1)))
                   (is (= (ctx-get-value ctx (make-variable "result")) (f-closed-form to-value))))))))
        ]
    (with-open [writer (io/writer "/tmp/basic-rewrite-bench-1.csv")]
      (csv/write-csv writer (cons ["problem size" "time in ns" "matches attempted" "rewrites performed" "rexpr created"]
                                   br)))))

(deftest basic-clojure-bench
  (let [br (run-benchmark
            (fn [to-value]
              (f-clojure to-value)))]
    (with-open [writer (io/writer "/tmp/basic-clojure-bench-1.csv")]
      (csv/write-csv writer (cons ["problem size" "time in ns" "matches attempted" "rewrites performed" "rexpr created"]
                                  br)))))

(deftest basic-jit-bench
  (println "test started " (-> (java.lang.management.ManagementFactory/getRuntimeMXBean)
                               (.getName)
                               (string/split #"@")
                               (first)))
  (Thread/sleep 5000)
  (tbinding
   [generate-new-jit-rewrites true]
   (let [rexpr (synthize-rexpr benchmark-rexpr)
         br (run-benchmark
             (fn [to-value]
               (let [ctx (context/make-empty-context rexpr)]
                 (ctx-set-value! ctx (make-variable "X") to-value)
                 (context/bind-context-raw
                  ctx
                  (let [res (simplify-fully rexpr)]
                    (is (= res (make-multiplicity 1)))
                    (is (= (ctx-get-value ctx (make-variable "result")) (f-closed-form to-value))))))))
         ]
     (with-open [writer (io/writer "/tmp/jit-rewrite-bench-1.csv")]
       (csv/write-csv writer (cons ["problem size" "time in ns" "matches attempted" "rewrites performed" "rexpr created"]
                                   br))))))

(deftest basic-rewriting
  (let [rexpr benchmark-rexpr
        to-value 10000
        ctx (context/make-empty-context rexpr)]
    (ctx-set-value! ctx (make-variable "X") to-value)
    (context/bind-context-raw
     ctx
     (let [res (simplify-fully rexpr)]
       (is (= res (make-multiplicity 1)))
       (debug-repl)
       (is (= (ctx-get-value ctx (make-variable "result")) (f-closed-form to-value)))
       ))))

(deftest jit-benchmark1
  (println "test"))
