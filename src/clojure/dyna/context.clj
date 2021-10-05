(ns dyna.context
  (:require [dyna.utils :refer :all])
  (:require [clojure.set :refer [union]])
  (:import (dyna UnificationFailure)))

(defprotocol RContext
  (get-rexpr [this])
  (get-value [this variable])
  (is-bound? [this variable])
  (set-value! [this variable value])
  (add-rexpr! [this rexpr])
  (add-context! [this other-context])
  (all-rexprs [this])
  (exit-context [this resulting-rexpr])
  ;(construct-context-rexpr [this])
  (intersect [this other])
  (subtract [this other])

  ;; for debugging
  (get-inner-values [this])
  (get-all-bindings [this])
  )




;; this is the current context which is dynamically rebound depending on what is currently running
;; this means that we are not passing this value around, which simplifies the calling api a bit
(def ^{:dynamic true :private true} *context*)

(defn get-context [] *context*)

(deftype context
  [parent
   root-rexpr
   ^:unsynchronized-mutable rexprs                          ; unsynchronized-mutable as this should only be used from a single thread
   ^:unsynchronized-mutable value-map]

  RContext
  (get-rexpr [this] root-rexpr)
  (get-value [this variable]
    (if (contains? value-map variable)
      (get value-map variable)
      (if (not (nil? parent)) (get-value parent variable))))
  (is-bound? [this variable]
    (or (not (nil? (get value-map variable)))
        (and (not (nil? parent)) (is-bound? parent variable))))
  (set-value! [this variable value]
    (let [current-value (get-value this variable)]
      (if (not (nil? current-value))
        (if (not= current-value value)
          (throw (UnificationFailure. "Value does not match")))
        (if (or (contains? value-map variable) (nil? parent))
          (set! value-map (assoc value-map variable value))
          (set-value! parent variable value)))))
  (add-rexpr! [this rexpr]
    (set! rexprs (conj rexprs rexpr)))
  (all-rexprs [this]
    (if (nil? parent)
      rexprs
      (union rexprs (.all-rexprs ^context parent))))
  ;; (construct-context-rexpr [this] nil)
    ;; the unification constraints are not going to be present in the expression, so we are going to have to
    ;(dyna.rexpr/make-conjunct (for [x value-map]
    ;                                    (dyna.rexpr/unify-rexpr. (car x) (cdar x)))))

  (get-inner-values [this] [parent root-rexpr rexprs value-map])
  (get-all-bindings [this] (merge (when parent (get-all-bindings parent))
                                  value-map))
  (intersect [this other]
    (???))
  (subtract [this other]
    (???))

  (add-context! [this other-context]
    (???))

  (exit-context [this resulting-rexpr]
    ;; (if (some some? (vals value-map))
    ;;   (debug-repl))
    resulting-rexpr)
  Object
  (toString ^String [this]
    (str "Context {" rexprs "}")))



(defn make-empty-context [rexpr]
  (context. nil rexpr #{rexpr} {}))

(defn make-nested-context [rexpr]
  (context. *context* rexpr #{rexpr} {}))

(defn make-nested-context-introduce-variable [rexpr variable]
  ;; this needs to somehow manage that there is a new context, which means that when
  ;; this context is destroyed, it should save the result of the expression
  ;;(debug-repl)
  (context. *context* rexpr #{rexpr} {variable nil}))

(defmethod print-method context [this ^java.io.Writer w]
  (.write w (.toString ^Object this)))

(defmacro bind-context [val & args]
  ;; this should remap any call to get-context to whatever is the new variable

  `(let [new-ctx# ~val
         resulting-rexpr# (binding [*context* new-ctx#]
                            ~@args)]
     ;; there should be some exit operation which can check if there is anything which should happen with the grounding
     (exit-context new-ctx# resulting-rexpr#)
     ))

(defmacro need-context [& args]
  `(if (bound? #'*context*)
     (do ~@args)))

(defn has-context [] (bound? #'*context*))



;; there could be some nested variables which are array list based
;; those variables would not have the
