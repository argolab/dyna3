(ns dyna-backend.gradient-numbers
  (:require [dyna-backend.utils :refer :all])
  (:import (dyna_backend TracedNumber)))

(defn make-number [^double x]
  (TracedNumber. x 0 (fn [z queue] nil)))

(defn add-to-gradient [num queue grad]
  (if (instance? TracedNumber num)
    (do (.addToGradient ^TracedNumber num grad)
        (.enqueue ^TracedNumber num queue))))

(defn- get-value [num]
  (if (instance? TracedNumber num)
    (.value ^TracedNumber num)
    num))

(defn- get-height
  ([] 0)
  ([num]
   (if (instance? TracedNumber num)
     (+ 1 (.height ^TracedNumber num))
     0))
  ([a & other]
   (max (get-height a) (get-height other))))


(defmethod print-method TracedNumber [^TracedNumber this ^java.io.Writer w]
          (.write w (.toString this)))

;
;(defn grad-add [a b]
;  (TracedNumber. (+ (get-value a) (get-value b))
;                 (get-height a b)
;                 (fn [z queue]
;                   (add-to-gradient a queue (.getGradient z))
;                   (add-to-gradient b queue (.getGradient z))
;                   )))
;
;(defn grad-mul [a b]
;  (TracedNumber. (* (get-value a) (get-value b))
;                 (get-height a b)
;                 (fn [z queue]
;                   (add-to-gradient a queue (* (get-value b) (.getGradient z)))
;                   (add-to-gradient b queue (* (get-value a) (.getGradient z))))))

(defn- add-get-values [params val]
  (if (contains? params val)
    `(get-value ~val)
    (map-same-type (partial add-get-values params) val)))


(defmacro defn-gradient-op [op params forward backwards]
  (let [all-args (set params)
        forward-mapped (add-get-values all-args forward)
        ;backward-mapped (add-get-values all-args backwards)
        ]
    `(defn ~op ~params
       (if (or ~@(for [p params] `(instance? TracedNumber ~p)))
         (TracedNumber. ~forward-mapped
                        (get-height ~@params)
                        (fn ~'[^TracedNumber gradv queue]
                          (let [~'grad (.getGradient ~'gradv)]
                            ~backwards)))

         ~forward)))
  )




(defn-gradient-op grad-add [a b]
                  (+ a b)
                  (do (add-to-gradient a queue grad)
                      (add-to-gradient b queue grad)))

(defn-gradient-op grad-mul [a b]
                  (* a b)
                  (do (add-to-gradient a queue (* grad (get-value b)))
                      (add-to-gradient b queue (* grad (get-value a)))))

(defn-gradient-op grad-div [a b]
                  (/ a b)
                  (do (add-to-gradient a queue (/ grad (get-value b)))
                      (add-to-gradient b queue (- (* grad (get-value a) (/ 1 (* (get-value b) (get-value b))))))))

(defn-gradient-op grad-sub [a b]
                  (- a b)
                  (do (add-to-gradient a queue grad)
                      (add-to-gradient b queue (- grad))))

(defn-gradient-op grad-sin [x]
                  (Math/sin x)
                  (add-to-gradient x queue (Math/cos grad)))

(defn-gradient-op grad-cos [x]
                  (Math/cos x)
                  (add-to-gradient x queue (- (Math/sin grad))))

(defn-gradient-op grad-tan [x]
                  (Math/tan x)
                  (add-to-gradient x queue (let [z (Math/cos grad)] (/ 1 (* z z)))))

(defn-gradient-op grad-exp [x]
                  (Math/exp x)
                  (add-to-gradient x queue (* grad (Math/exp (get-value x)))))


(defn-gradient-op grad-abs [x]
                  (if (< x 0) (- x) x)
                  (add-to-gradient x queue (* grad (if (< x 0) -1 1))))

(defn-gradient-op grad-pow [x e]
                  (Math/pow x e)
                  (do (add-to-gradient x queue (* grad e (Math/pow x (- e 1))))
                      (add-to-gradient e queue 99999999)))

(defn grad-max [a b]
  (if (> (get-value a) (get-value b))
    a b))

(defn grad-min [a b]
  (if (> (get-value a) (get-value b))
    b a))

;; operations which do not directly influence the numerical values, do not need gradients, as those will
;; change the shape of the graph.  So this would have that there are some of which

(defn set-loss-compute-grad [num]
  (if (instance? TracedNumber num)
    (TracedNumber/runBackprop num)))
