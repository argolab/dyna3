(ns dyna.context
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [clojure.set :refer [union intersection difference]])
  (:import [dyna UnificationFailure RContext ContextHandle])
  (:require [dyna.rexpr-constructors :refer :all]))


;; this is the current context which is dynamically rebound depending on what is currently running
;; this means that we are not passing this value around, which simplifies the calling api a bit
#_(def ^{:dynamic true :private true} *context*)

;; global variable which sets the full-context variable on the context.  The
;; full context tracks /all/ conjunctive constraints rather than just the easy
;; constraints
;(def ^{:dynamic true :private true} *use-full-context* false)

(defn- make-variable-assignment-conjunct [value-map]
  (make-conjunct (into [] (for [[k v] value-map]
                            (make-no-simp-unify k (make-constant v))))))

(defn get-context
  {:inline (fn [] `(ContextHandle/get))}
  []
  (ContextHandle/get))
(defn- get-context-bound []
  (let [c (ContextHandle/get)]
    (assert (not (nil? c)))
    c))

;(def context-set-value-history {})

(deftype context
    [parent
     ;full-context ; if true, then this is tracking all conjuncts, otherwise this is just the assignments to variables
                  ; this is currently getting ignored, so we are essentially always having the full context
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
    (let [v (get value-map variable :not-found-in-map)]
      (if (= v :not-found-in-map)
        (and (not (nil? parent)) (ctx-is-bound? parent variable))
        (not (nil? v)))))
  ;; TODO: there should be a recursive version of the set-value! function which avoids rechecking what the current
  ;; value of the variable is
  (ctx-set-value! [this variable value]
    #_(when (.contains (str variable) "agg-op-hidden23628")
      (debug-repl "setting h var"))
    (assert (not (nil? value)))
    (let [current-value (ctx-get-value this variable)]
      (if-not (nil? current-value)
        (when (not= current-value value)
          (throw (UnificationFailure. "Value does not match")))
        ;; then depending on the kind of context this is, we might have different behavior of
        ;; setting the value of the variable.
        (if (or (contains? #{:root :disjunct :aggregator :if-expr-coditional :memo-expr-conditional :aggregator-op-outer
                             } context-kind)
                (and (contains? #{:aggregator-conjunctive :proj :aggregator-op-inner} context-kind)
                     (contains? value-map variable)))
          ;; then we set the value locally
          (do (set! value-map (assoc value-map variable value))
              ;(def context-set-value-history (assoc context-set-value-history variable [value (Throwable.)]))
              )
          ;; then we are going to pass this up to something else
          (ctx-set-value! parent variable value)))))
  (ctx-add-rexpr! [this rexpr]
    (set! rexprs (conj rexprs rexpr)))
  (ctx-all-rexprs [this]
    (if (nil? parent)
      rexprs
      (union rexprs (.ctx-all-rexprs ^context parent))))

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
    (cond
      ;; the root context is the top level, when we exit, this is either getting stored or returned to the user
      (= context-kind :root) (make-conjunct [(make-variable-assignment-conjunct value-map)
                                             resulting-rexpr])
      (= context-kind :disjunct) (if-not (empty? value-map)
                                   ;; then we have to save the value of these variables into the R-expr
                                   (make-conjunct [(make-variable-assignment-conjunct value-map)
                                                   resulting-rexpr])
                                   resulting-rexpr)  ;; there is nothing to add to this expression

      (= context-kind :proj) (let [proj-var (:var root-rexpr)]
                               (assert (empty? (dissoc value-map proj-var))) ;; all of the other variable assignments should have already been propagated out
                               resulting-rexpr) ;;

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
                                                   (doseq [rx rexprs]
                                                     (when-not (some #{incoming-var} (get-variables rx))
                                                       (ctx-add-rexpr! parent rx))))
                                                 resulting-rexpr)
      (= context-kind :memo-expr-conditional) resulting-rexpr  ;; I suppose this will just reset after it runs
      (= context-kind :aggregator-op-inner) (do
                                              ;; Any variable that is bound will be remapped by the aggregator itself, we do not need to anything here
                                              resulting-rexpr)
      (= context-kind :aggregator-op-outer) (do
                                              [value-map resulting-rexpr])
      #_(if (empty? value-map)
          resulting-rexpr
          (do
            (assert (empty? value-map))
            resulting-rexpr
            #_(when value-map
                (debug-repl "agg outer")
                (???)) ;; this is wrong.  Nothing is projected with outer.  All of the values should just "float up"
            #_(make-conjunct [(make-variable-assignment-conjunct value-map)
                              resulting-rexpr])))
      :else (do
              (dyna-debug (debug-repl "context unknown kind"))
              (???))))  ;; todo: other kinds of contexts which are going

  (ctx-scan-through-conjuncts [this scan-fn]
    (let [r (first (remove nil? (map scan-fn rexprs)))]
      (if (and (nil? r) (not (nil? parent)))
        (ctx-scan-through-conjuncts parent scan-fn)
        r)))

  (ctx-contains-rexpr? [this rexpr]
    (or (contains? rexprs rexpr)
        (if-not (nil? parent)
          (ctx-contains-rexpr? parent rexpr)
          false)))

  (ctx-get-value-map-upto-context [this parent-context]
    (if (identical? this parent-context)
      nil
      (merge (when parent (ctx-get-value-map-upto-context parent parent-context))
             value-map)))

  Object
  (toString ^String [this]
    (if (nil? parent)
      (str "Context" context-kind " {" value-map "}")
      (str "Context" context-kind " {" value-map ", <" (.toString parent) ">}"))))



(defn make-empty-context [rexpr]
  (context. nil  :root rexpr #{rexpr} {}))

(defn make-nested-context-disjunct [rexpr]
  (context. (get-context-bound) :disjunct rexpr #{rexpr} {}))

(defn make-nested-context-proj [rexpr variables]
  (context. (get-context-bound) :proj rexpr #{rexpr} (into {} (map (fn [x] [x nil]) variables))))

(defn make-nested-context-if-conditional [rexpr]
  (context. (get-context-bound) :if-expr-conditional rexpr #{rexpr} {}))

(defn make-nested-context-aggregator [rexpr incoming-var is-conjunctive-aggregator]
  (let [pcontext (get-context-bound)]
    (context. pcontext
              (if is-conjunctive-aggregator
                :aggregator-conjunctive  ;; this would mean that we can push through assignments of variables to variables which are outside of this expression.  If something is
                :aggregator)
              rexpr #{rexpr}
              (if (ctx-is-bound? pcontext incoming-var)
                {}  ;; the incoming variable is already bound, so we will want
                    ;; to read the value out of the parent context instead of
                    ;; creating a local slot for this variable.  This can
                    ;; happenin the case that the incoming
                {incoming-var nil}))))


(defn make-nested-context-memo-conditional [rexpr]
  (context. (get-context-bound) :memo-expr-conditional rexpr #{rexpr} {}))

(defn make-nested-context-aggregator-op-outer [rexpr]
  (context. (get-context-bound)  :aggregator-op-outer rexpr #{rexpr}
            {}))

(defn make-nested-context-aggregator-op-inner [rexpr projected-vars incoming-var]
  (context. (get-context-bound) :aggregator-op-inner rexpr #{rexpr} (into {incoming-var nil} (for [v projected-vars] [v nil]))))

(defmethod print-method context [this ^java.io.Writer w]
  (.write w (.toString ^Object this)))

(defmacro bind-context [val & args]
  ;; this should remap any call to get-context to whatever is the new variable

  `(let [new-ctx# ~val
         old-ctx# (ContextHandle/get)]
     (dyna-assert (and (instance? RContext new-ctx#)
                       (not (nil? new-ctx#))))
     (let [resulting-rexpr#
           (try
             (do
               (ContextHandle/set new-ctx#)
               ~@args)
             (finally
               (ContextHandle/set old-ctx#)))]
       ;; there should be some exit operation which can check if there is anything which should happen with the grounding
       (ctx-exit-context new-ctx# resulting-rexpr#))))

(defmacro bind-context-raw [val & args]
  `(let [new-ctx# ~val
         old-ctx# (ContextHandle/get)]
     (dyna-assert (and (instance? RContext new-ctx#)
                       (not (nil? new-ctx#))))
     (try
       (do
         (ContextHandle/set new-ctx#)
         ~@args)
       (finally
         (ContextHandle/set old-ctx#)))))

(defmacro bind-no-context [& args]
  `(let [old-ctx# (ContextHandle/get)]
     (try
       (do
         (ContextHandle/set nil)
         ~@args)
       (finally
         (ContextHandle/set old-ctx#)))))

(defn has-context [] (not (nil? (get-context))))

(defmacro need-context [& args]
  `(if (has-context)
     (do ~@args)))


(swap! debug-useful-variables assoc 'context get-context)


;; these should be replaced with something that is more efficient.  like if this is going to require
(defmacro scan-through-full-context [ctx argument & body]
  ;; scan through all of the conjunctive constraints in the context and assign them to the argument variable
  ;; keep scanning as long as body does not return nil, otherwise return the value from body
  `(let [scan-fun# (fn [~argument] ~@body)]
     (ctx-scan-through-conjuncts ~ctx scan-fun#)))

;; these methods should be made more efficient in the future, for now, they are
;; just going to scan through the full list of conjunctive constraints and
;; filter out the things which are not relevant.  This is _not_ efficient atm.

(defmacro scan-through-context-by-type [ctx type argument & body]
  ;; scan through the conjunctive constraitns which are of the rexpr argument `type`
  ;; the value will be bound to the argument variable
  ;; keep scanning as long as the body return nil.  if the result is not nil, then that will be returned
  `(let [scan-fun# (fn [~argument] (when (instance? ~type ~argument)
                                      ~@body))]
     (ctx-scan-through-conjuncts ~ctx scan-fun#)))


(defmacro scan-through-context-by-variable [ctx variable argument & body]
  ;; many constraints are going to be looking to find other things which interact with a specific variable

  `(let [var# ~variable
         scan-fun# (fn [~argument] (when (contains? (exposed-variables ~argument) var#)
                                     ~@body))]
     (ctx-scan-through-conjuncts ~ctx scan-fun#)))


(swap! debug-useful-variables assoc 'all-context-conjuncts
       (fn []
         (fn [] (let [ret (transient #{})]
                  (scan-through-full-context (get-context) a (conj! ret a))
                  (persistent! ret)))))
