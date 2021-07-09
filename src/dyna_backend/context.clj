(ns dyna-backend.context
  (:require [dyna-backend.utils :refer :all])
  (:require [clojure.set :refer [union]])
  )

(defprotocol RContext
  (get-rexpr [this])
  (get-value [this variable])
  (is-bound? [this vraiable])
  (set-value! [this variable value])
  (add-rexpr! [this rexpr])
  (all-rexprs [this])
  )

;; this is the current context which is dynamically rebound depending on what is currently running
;; this means that we are not passing this value around, which simplifies the calling api a bit
(def ^:dynamic *context*)

(deftype context
    [parent
     root-rexpr
     ^:unsynchronized-mutable rexprs ; unsynchronized-mutable as this should only be used from a single thread
     ^:unsynchronized-mutable value-map
     ]
  RContext
  (get-rexpr [this] root-rexpr)
  (get-value [this variable]
    (if (contains? value-map variable)
      (get value-map variable)
      (and (not (nil? parent)) (.get-value parent variable))))
  (is-bound? [this variable]
    (or (contains? value-map variable)
        (and (not (nil? parent)) (is-bound? parent variable))))
  (set-value! [this variable value]
    (set! value-map (assoc value-map variable value)))
  (add-rexpr! [this rexpr]
    (set! rexprs (conj rexprs rexpr)))
  (all-rexprs [this]
    (if (nil? parent)
      rexprs
      (union rexprs (.all-rexprs parent))))
  )

(defn make-empty-context [rexpr]
  (context. nil rexpr #{rexpr} {}))

(defn make-nested-context [&context rexpr]
  (context. &context rexpr #{rexpr} {}))

(defn make-nested-context-introduce-variable [&context rexpr variable]
  ;; this needs to somehow manage that there is a new context, which means that when
  ;; this context is destroyed, it should save the result of the expression
  (assert false)
  (context. &context rexpr #{rexpr} {}))

(defmacro bind-context [val & args]
  `(binding [*context* ~val]
     ~@args))
