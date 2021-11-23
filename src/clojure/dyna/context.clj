(ns dyna.context
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [clojure.set :refer [union intersection difference]])
  (:import (dyna UnificationFailure)))


;; this is the current context which is dynamically rebound depending on what is currently running
;; this means that we are not passing this value around, which simplifies the calling api a bit
(def ^{:dynamic true :private true} *context*)

(defn get-context [] *context*)


(deftype context
    [parent
     context-kind
     root-rexpr
     ^:unsynchronized-mutable rexprs                          ; unsynchronized-mutable as this should only be used from a single thread
     ^:unsynchronized-mutable value-map]

  RContext
  (ctx-get-rexpr [this] root-rexpr)
  (ctx-get-value [this variable]
    (if (contains? value-map variable)
      (get value-map variable)
      (if (not (nil? parent)) (ctx-get-value parent variable))))
  (ctx-is-bound? [this variable]
    (or (not (nil? (get value-map variable)))
        (and (not (nil? parent)) (ctx-is-bound? parent variable))))
  ;; TODO: there should be a recursive version of the set-value! function which avoids rechecking what the current
  ;; value of the variable is
  (ctx-set-value! [this variable value]
    (assert (not (nil? value)))
    (let [current-value (ctx-get-value this variable)]
      (if-not (nil? current-value)
        (when (not= current-value value)
          (throw (UnificationFailure. "Value does not match")))
        ;; then depending on the kind of context this is, we might have different behavior of
        ;; setting the value of the variable.
        (if (or (contains? #{:root :disjunct :aggregator :if-expr-coditional} context-kind)
                (and (contains? #{:aggregator-conjunctive :proj} context-kind)
                     (contains? value-map variable)))
          ;; then we set the value locally
          (set! value-map (assoc value-map variable value))
          ;; then we are going to pass this up to something else
          (ctx-set-value! parent variable value)))))

  (ctx-add-rexpr! [this rexpr]
    (set! rexprs (conj rexprs rexpr)))
  ;; (add-context! [this other]
  ;;   (assert (identical? parent (.-parent ^context other)))
  ;;   (set! rexprs (conj rexprs (.-rexprs ^context other)))
  ;;   (set! value-map (conj value-map (.-value-map ^context other))))
  (ctx-all-rexprs [this]
    (if (nil? parent)
      rexprs
      (union rexprs (.all-rexprs ^context parent))))
  ;; (construct-context-rexpr [this] nil)
    ;; the unification constraints are not going to be present in the expression, so we are going to have to
    ;(dyna.rexpr/make-conjunct (for [x value-map]
    ;                                    (dyna.rexpr/unify-rexpr. (car x) (cdar x)))))

  (ctx-get-inner-values [this] [parent context-kind root-rexpr rexprs value-map])
  (ctx-get-all-bindings [this] (merge (when parent (ctx-get-all-bindings parent))
                                  value-map))

  ;; these methods are likely inefficient, currently just placeholder implementations here
  (ctx-intersect [this other]
    (assert (identical? parent (.-parent ^context other)))
    (context. parent context-kind nil ;; if there are two rexprs here, then there is no root-rexpr for this
              (intersection rexprs (.-rexprs ^context other))
              (into {} (intersection (into #{} (seq value-map))
                                     (into #{} (seq (.-value-map ^context other)))))))
  (ctx-subtract [this other]  ;; return this - other.  Meaning that parent should be the other
    (assert (identical? parent (.-parent ^context other)))
    (context. parent context-kind nil ;; what is the r-rexpr which is represented here?
              (difference rexprs (.-rexprs ^context other))
              (into {} (difference (into #{} (seq value-map))
                                   (into #{} (seq (.-value-map ^context other)))))))

  (ctx-add-context! [this other-context]
    (set! rexprs (union rexprs (.-rexprs ^context other-context)))
    (doseq [[k v] (.-value-map ^context other-context)]
      (ctx-set-value! this k v)))

  (ctx-exit-context [this resulting-rexpr]
    ;; this should push to the parent anything that is relevant.  If the expression would have that
    ;; there are some

    ;; (if (some some? (vals value-map))
    ;;   (debug-repl))
    resulting-rexpr)
  Object
  (toString ^String [this]
    (str "Context {" value-map "}")))



(defn make-empty-context [rexpr]
  (context. nil :root rexpr #{rexpr} {}))

(defn make-nested-context-disjunct [rexpr]
  (assert (bound? #'*context*))
  (context. *context* :disjunct rexpr #{rexpr} {}))

(defn make-nested-context-proj [rexpr variables]
  (assert (bound? #'*context*))
  (context. *context* :proj rexpr #{rexpr} (into {} (map (fn [x] [x nil]) variables))))

(defn make-nested-context-if-conditional [rexpr]
  (assert (bound? #'*context*))
  (context. *context* :if-expr-conditional rexpr #{rexpr} {}))

(defn make-nested-context-aggregator [rexpr incoming-var is-conjunctive-aggregator]
  (assert (bound? #'*context*))
  (context. *context*
            (if is-conjunctive-aggregator
              :aggregator-conjunctive  ;; this would mean that we can push through assignments of variables to variables which are outside of this expression.  If something is
              :aggregator)
            rexpr #{rexpr} {incoming-var nil}))

(defmethod print-method context [this ^java.io.Writer w]
  (.write w (.toString ^Object this)))

(defmacro bind-context [val & args]
  ;; this should remap any call to get-context to whatever is the new variable

  `(let [new-ctx# ~val]
     (assert (satisfies? RContext new-ctx#))
     (let [resulting-rexpr# (binding [*context* new-ctx#]
                              ~@args)]
       ;; there should be some exit operation which can check if there is anything which should happen with the grounding
       (ctx-exit-context new-ctx# resulting-rexpr#))))

(defmacro bind-context-raw [val & args]
  `(let [new-ctx# ~val]
     (binding [*context* new-ctx#]
       ~@args)))

(defmacro bind-no-context [& args]
  `(binding [*context* nil]  ;; not 100% sure if we can "unbind" the context, maybe should just make the "root" nil and just check the nil value
     ~@args))

(defn has-context [] (and (bound? #'*context*)
                          (not (nil? *context*))))

(defmacro need-context [& args]
  `(if (has-context)
     (do ~@args)))



;; there could be some nested variables which are array list based
;; those variables would not have the
