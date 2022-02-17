(ns dyna.context
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [clojure.set :refer [union intersection difference]])
  (:import (dyna UnificationFailure))
  (:require [dyna.rexpr-constructors :refer :all]))


;; this is the current context which is dynamically rebound depending on what is currently running
;; this means that we are not passing this value around, which simplifies the calling api a bit
(def ^{:dynamic true :private true} *context*)

;; global variable which sets the full-context variable on the context.  The
;; full context tracks /all/ conjunctive constraints rather than just the easy
;; constraints
(def ^{:dynamic true :private true} *use-full-context* false)

(defn- make-variable-assignment-conjunct [value-map]
  (make-conjunct (into [] (for [[k v] value-map]
                            (make-no-simp-unify k (make-constant v))))))

(defn get-context [] *context*)


(deftype context
    [parent
     full-context ; if true, then this is tracking all conjuncts, otherwise this is just the assignments to variables
     context-kind
     root-rexpr
     ^:unsynchronized-mutable rexprs                          ; unsynchronized-mutable as this should only be used from a single thread
     ^:unsynchronized-mutable value-map]

  RContext
  (ctx-get-rexpr [this] root-rexpr)
  (ctx-get-value [this variable]
    (if (contains? value-map variable)
      (get value-map variable)
      (if (not (nil? parent))
        (ctx-get-value parent variable))))
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
    (context. parent full-context context-kind nil ;; if there are two rexprs here, then there is no root-rexpr for this
              (intersection rexprs (.-rexprs ^context other))
              (into {} (intersection (into #{} (seq value-map))
                                     (into #{} (seq (.-value-map ^context other)))))))
  (ctx-subtract [this other]  ;; return this - other.  Meaning that parent should be the other
    (assert (identical? parent (.-parent ^context other)))
    (context. parent full-context context-kind nil ;; what is the r-rexpr which is represented here?
              (difference rexprs (.-rexprs ^context other))
              (into {} (difference (into #{} (seq value-map))
                                   (into #{} (seq (.-value-map ^context other)))))))

  (ctx-add-context! [this other-context]
    (set! rexprs (union rexprs (.-rexprs ^context other-context)))
    (doseq [[k v] (.-value-map ^context other-context)]
      (ctx-set-value! this k v)))

  (ctx-exit-context [this resulting-rexpr]
    (cond
      ;; the root context is the top level, when we exit, this is either getting stored or returned to the user
      (= context-kind :root) (make-conjunct [(make-variable-assignment-conjunct value-map)
                                             resulting-rexpr])
      (and (= context-kind :disjunct) (not full-context)) (if-not (empty? value-map)
                                                            ;; then we have to save the value of these variables into the R-expr
                                                            (make-conjunct [(make-variable-assignment-conjunct value-map)
                                                                            resulting-rexpr])
                                                            resulting-rexpr  ;; there is nothing to add to this expression
                                                            )
      (= context-kind :proj) (let [proj-var (:var root-rexpr)]
                               (assert (empty? (dissoc value-map proj-var))) ;; all of the other variable assignments should have already been propagated out
                               resulting-rexpr ;;
                               )
      ;; (do (debug-repl)
                             ;;   (let [proj-var (:var root-rexpr)]
                             ;;       (if (contains? value-map proj-var)
                             ;;         (???) ;; then this should propagate the value of this variable into the R-expr and remove this projection.  but that should get handled
                             ;;         resulting-rexpr)))
      (= context-kind :aggregator-conjunctive) (let [incoming-var (:incoming root-rexpr)]
                                                 (assert (:body-is-conjunctive root-rexpr)) ;; double check that the root is conjunctive
                                                 ;; any constraints which do not reference the incoming variable can be added to the outer context
                                                 (when-not (nil? parent)
                                                   (doseq [[var val] value-map]
                                                     (when (not= incoming-var var)
                                                       (ctx-set-value! parent var val)))
                                                   (when full-context
                                                     (doseq [rx rexprs]
                                                       (when-not (contains? (get-variables rx) incoming-var)
                                                         (ctx-add-rexpr! parent rx)))))
                                                 resulting-rexpr)
      :else (do
              (debug-repl)
              (???))  ;; todo: other kinds of contexts which are going
      ))
  Object
  (toString ^String [this]
    (if (nil? parent)
      (str "Context" context-kind " {" value-map "}")
      (str "Context" context-kind " {" value-map ", <" (.toString parent) ">}"))))



(defn make-empty-context [rexpr]
  (context. nil *use-full-context* :root rexpr #{rexpr} {}))

(defn make-nested-context-disjunct [rexpr]
  (assert (bound? #'*context*))
  (context. *context* *use-full-context* :disjunct rexpr #{rexpr} {}))

(defn make-nested-context-proj [rexpr variables]
  (assert (bound? #'*context*))
  (context. *context* *use-full-context* :proj rexpr #{rexpr} (into {} (map (fn [x] [x nil]) variables))))

(defn make-nested-context-if-conditional [rexpr]
  (assert (bound? #'*context*))
  (context. *context* *use-full-context* :if-expr-conditional rexpr #{rexpr} {}))

(defn make-nested-context-aggregator [rexpr incoming-var is-conjunctive-aggregator]
  (assert (bound? #'*context*))
  (let [pcontext *context*]
    (context. pcontext *use-full-context*
              (if is-conjunctive-aggregator
                :aggregator-conjunctive  ;; this would mean that we can push through assignments of variables to variables which are outside of this expression.  If something is
                :aggregator)
              rexpr #{rexpr}
              (if (ctx-is-bound? pcontext incoming-var)
                {}  ;; the incoming variable is already bound, so we will want
                    ;; to read the value out of the parent context instead of
                    ;; creating a local slot for this variable.  This can
                    ;; happenin the case that the incoming
                {incoming-var nil})
              )))

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
     (assert (satisfies? RContext new-ctx#))
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


(swap! debug-useful-variables assoc 'context get-context)



;; there could be some nested variables which are array list based
;; those variables would not have the
