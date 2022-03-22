(ns dyna.iterators
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all]))

;; iterators are going to allow for there to efficiently loop over the values which are assigned to variables

;; should the iterators assume the context?  in which case it can have that the
;; iterator can just set values into the context when it is doing iteration.  If
;; we don't assume a context, then we will find that there is some

;; the context should eventually be something that can be represented as an
;; array or some "efficient" structure where we can access different fields.
;; This means that we would like to be able to have that the iterator will not
;; be tied to using the variable name (per-se), or there should be some

(defprotocol DIterable
  (iter-what-variables-bound [this])
  (iter-variable-binding-order [this])

  (iter-create-iterator [this which-binding]))


;; this could be like a map function?  This would have that it returns a
;; possibly lazy serquence over the values returned by the run-cb?
;; this will want to find which of the values will have this binding
(defprotocol DIterator
  (iter-run-cb [this cb-fun])
  (iter-has-next [this]))


;; (deftype union-iterator [iter1 iter2]
;;   ())

;; (deftype unit-iterator [variable value]
;;   DIterator

;;   )

(defn make-unit-iterator [variable value]
  #{(reify DIterable
      (iter-what-variables-bound [this] #{variable})
      (iter-variable-binding-order [this] [[variable]]) ;; could do something like {#{} #{variable}}
      (iter-create-iterator [this which-binding] (reify DIterator
                                                   (iter-run-cb [this cb-fun] (cb-fun {variable value}))
                                                   (iter-has-next [this] false))))})
