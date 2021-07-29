(ns dyna-backend.gradient-numbers
  (:require [dyna-backend.utils :refer :all])
  (:import (dyna_backend TracedNumber)))

(defn make-number [^double x]
  (TracedNumber. x 0 (fn [z queue] nil)))

(defn add-to-gradient [num queue grad]
  (if (instance? TracedNumber num)
    (do (.addToGradient num grad)
        (.enqueue num queue))))

(defn- get-value [num]
  (if (instance? TracedNumber num)
    (.value num)
    num))

(defn- get-height
  ([] 0)
  ([num]
   (if (instance? TracedNumber num)
     (+ 1 (.height num))
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
        backward-mapped (add-get-values all-args backwards)
        ] `(defn ~op ~params
                     (if (or ~@(for [p params] `(instance? TracedNumber ~p)))
                       (TracedNumber. ~forward-mapped
                                      (get-height ~@params)
                                      (fn [^TracedNumber gradv queue]
                                        (let [grad (.getGradient gradv)]
                                          ~backward-mapped)
                                        )
                                      )
                       forward
                       )
                    ))
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
                  (sin x)
                  (add-to-gradient x queue (cos grad)))

(defn-gradient-op grad-cos [x]
                  (cos x)
                  (add-to-gradient x queue (- (sin grad))))

(defn-gradient-op grad-tan [x]
                  (tan x)
                  (add-to-gradient x queue (let [z (cos grad)] (/ 1 (* z z)))))

(defn-gradient-op grad-exp [x]
                  (exp x)
                  (add-to-gradient x queue (* grad (exp (get-value x)))))



(defn set-loss-compute-grad [num]
  (if (instance? TracedNumber num)
    (TracedNumber/runBackprop num)
    )
  )