;; This is the JIT compiler for R-exprs.  This is disabled by default.  To enable pass `-Ddyna.enable_jit=true` as a command line argument

(ns dyna.rexpr-jit-v2
  (:require [dyna.utils :refer :all])
  (:require [aprint.core :refer [aprint]])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-disjunction]) ;; make sure is loaded first
  (:require [dyna.rexpr-aggregators-optimized :refer [convert-basic-aggregator-to-op-aggregator]])
  (:require [dyna.rexpr-constructors :refer [is-disjunct-op?
                                             get-user-term
                                             is-aggregator-op-outer?
                                             is-aggregator-op-inner?
                                             make-no-simp-aggregator-op-inner
                                             make-no-simp-aggregator-op-outer]])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.rexpr-pretty-printer :refer [rexpr-printer]])
  (:require [dyna.prefix-trie :as trie])
  (:require [dyna.iterators :as iterators])
  (:require [clojure.walk :refer [macroexpand-all]])
  (:require [clojure.set :refer [union subset? intersection]])
  (:import [dyna.rexpr proj-rexpr simple-function-call-rexpr conjunct-rexpr disjunct-rexpr constant-value-rexpr])
  (:import [dyna.rexpr_aggregators_optimized aggregator-op-outer-rexpr aggregator-op-inner-rexpr])
  (:import [dyna.rexpr_aggregators Aggregator])
  (:import [dyna RexprValue RexprValueVariable Rexpr DynaJITRuntimeCheckFailed StatusCounters UnificationFailure DIterator ContextHandle ThreadVar RContext IteratorBadBindingOrder SimplifyRewriteCollection RexprValueVariableForceExposed]))

;; this is going to want to cache the R-expr when there are no arguments which are "variables"
;; so something like multiplicy can be just a constant value


;; map from the name of the jitted rexpr -> to the metadata which was used during construction
(def ^:private rexprs-types-constructed (atom {}))

(def ^:private rexpr-map-to-jit-hash-group (atom {}))

(declare ^:private is-bound-jit?)
;(println "TODO: jit-local-variable-rexpr should also be \"allowed\" to be a normal variable as long as it is projected out")

(defn- check-argument-diterator [x]
  (or (not (is-constant? x))
      (instance? DIterator (get-value x))))

(defn- assoc-make-binding-map
  ([] {})
  ([a b] {a b})
  ([a b & args] (assoc (apply assoc-make-binding-map args) a b)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ^:private bad-gen [& args] (throw (RuntimeException. "BAD code generation.  Attempted to use some code in the generated output which should have never been used")))

(def ^{:private true :dynamic true} *jit-generating-rewrite-for-rexpr* nil
  ;; set to the root R-expr which we are creating a rewrite for
  )
(defn- jit-generating-rewrite-for-rexpr-type []
  (if (string? *jit-generating-rewrite-for-rexpr*)
    *jit-generating-rewrite-for-rexpr*
    (.getName (type *jit-generating-rewrite-for-rexpr*))))

(def ^{:private true :dynamic true} *jit-generating-in-context* nil
  ;; set to the context which the root R-expr is present in
  )

(def ^{:private true :dynamic true} *current-assignment-to-exposed-vars* {}
  ;; variables which are exposed will have some current value.  These values can be looked up using the *jit-generating-in-context*
  ;; with this indirecting through what needs to happen for a given value

  ;; used by jit-evaluate-cljform
  )

(def ^{:private true :dynamic true} *local-variable-names-for-variable-values* nil;(volatile! nil)
  ;; values from variables which have been read can be stored in a local variable.  these variables can just read from these local variables instead of looking through the context
  ;; if a variable value's is read, then it should get saved to a local variable somewhere

  ;; used by jit-evaluate-cljform
  )

(def ^{:private true :dynamic true} *rewrites-allowed-to-run* #{:construction :standard}
  ;; which rewrites are we allowed to attempt to run at this point the inference
  ;; rewrites might not be run all of the time depending on if we are building a
  ;; "standard" rewrite or an "inference" rewrite
  )

(def ^{:private true :dynamic true} *rewrites-allowed-to-use-inference-context* false
  ;; we can perform inferences inside of the JITted context, however when
  ;; dealing with the outer context this will only look at variable bindings
  ;; unless this value is true.  The reason is that those inferences are still allowed to run when "fast"
  )


(def ^{:private true :dynamic true} *local-conjunctive-rexprs-for-infernece* nil
  ;; local R-exprs which are conjunctive which can also be used for inference
  )
(def ^{:private true :dynamic true} *jit-consider-expanding-placeholders* false
  ;; If we want embed the placeholder in the resulting JITted type.
  )
(def ^{:private true :dynamic true} *jit-call-simplify-on-placeholders* true
  ;; if we want to generate a call to simplify on the nested expressions
  )

(def ^{:private true :dynamic true} *rewrite-ns*
  ;; the namespace that the current rewrite was originally constructed in
  (find-ns 'dyna.rexpr-jit-v2))

(def ^{:private true :dynamic true} *locally-bound-variables* {}
  ;; the variable names are going to be given new generated names, so we need to track some mapping here
  )


(def ^{:private true :dynamic true} *rexpr-checked-already* nil
  ;; R-exprs which have already been checked and found to be true.  We do not want to infer an R-expr which then gets check and then just cycle
  ;; in the rewrites that we generate, so anytime that an R-expr is rewritten as mult-1, we will track it as "already checked"
  )


(def ^{:private true :dynamic true} *preconditions-known-true* #{})

(def ^{:private true :dynamic true} *jit-simplify-call-counter* nil)
(def ^{:private true :dynamic true} *jit-simplify-rewrites-found* nil)
(def ^{:private true :dynamic true} *jit-simplify-rewrites-picked-to-run* (constantly false))

(def ^{:private true :dynamic true} *jit-generate-functions* nil)

(def ^{:private true :dynamic true} *jit-incremented-status-counter* nil)

(def ^{:private true :dynamic true} *jit-computing-match-of-rewrite* nil)
(def ^{:private true :dynamic true} *jit-currently-rewriting* nil)
(def ^{:private true :dynamic true} *jit-rexpr-rewrite-metadata*)

;(def ^{:private true :dynamic true} *jit-before-performing-rewrite* (fn [rexpr rewrite]))
(def ^{:private true :dynamic true} *jit-compute-unification-failure* false)

(def ^{:private true :dynamic true} *jit-inside-disjunct* false)

(def ^{:private true :dynamic true} *jit-consider-current-value* true)

(def ^{:private true :dynamic true} *jit-variable-types-work-normally* false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare ^:private get-current-value jit-evaluate-cljform)


(defrecord jit-local-variable-rexpr [local-var-symbol]
  ;; These variables are not exposed externally.  These variables are projected
  ;; out before they reach the top.  We are going to give these variables a name
  ;; when we synthize the R-expr such that we will be able to track them in the
  ;; context of the program
  RexprValueVariable
  (get-value [this] (if-not *jit-variable-types-work-normally*
                      (???)
                      (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (get-value-in-context [this ctx] (if-not *jit-variable-types-work-normally*
                                     (???)
                                     (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] (is-bound-jit? this))
  (is-bound-in-context? [this ctx] (is-bound-jit? this))
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    (???))
  Object
  (toString [this] (str "(jit-local-variable " local-var-symbol ")")))

(defmethod print-dup jit-local-variable-rexpr [^jit-local-variable-rexpr j ^java.io.Writer w]
  (.write w "(dyna.rexpr_jit_v2.jit-local-variable-rexpr. (quote ")
  (print-dup (.local-var-symbol j) w)
  (.write w "))"))

(defrecord jit-expression-variable-rexpr [cljcode]
  RexprValueVariable
  (get-value [this] (if-not *jit-variable-types-work-normally*
                      (???)
                      (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (get-value-in-context [this ctx] (if-not *jit-variable-types-work-normally*
                                     (???)
                                     (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] true)
  (is-bound-in-context? [this ctx] true)
  (all-variables [this] #{})
  (get-representation-in-context [this ctx]
    (???))
  RexprValueVariableForceExposed
  Object
  (toString [this] (str "(jit-expression-variable " cljcode ")")))

(defmethod print-dup jit-expression-variable-rexpr [^jit-expression-variable-rexpr j ^java.io.Writer w]
  (.write w (str "(dyna.rexpr_jit_v2.jit-expression-variable-rexpr. (quote "
                 (.cljcode j)
                 " ))")))


(defmethod print-method jit-local-variable-rexpr [^jit-local-variable-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))

(defrecord jit-exposed-variable-rexpr [exposed-name]
  ;; For variables which are exposed on the current synthized R-expr.  These
  ;; variables can be access by doing `(. rexpr ~exposed-name) to read a field
  ;; off of the R-expr
  RexprValueVariable
  (get-value [this] (if-not *jit-variable-types-work-normally*
                      (???)
                      (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (get-value-in-context [this ctx] (if-not *jit-variable-types-work-normally*
                                     (???)
                                     (get-current-value (jit-evaluate-cljform `(get-value ~this)))))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] (get-current-value (jit-evaluate-cljform `(is-bound? ~this))))
  (is-bound-in-context? [this ctx] (get-current-value (jit-evaluate-cljform `(is-bound? ~this))))
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    this)
  RexprValueVariableForceExposed
  Object
  (toString [this] (str "(jit-exposed-variable-rexpr " exposed-name ")")))

(defmethod print-dup jit-exposed-variable-rexpr [^jit-exposed-variable-rexpr j ^java.io.Writer w]
  (.write w "(dyna.rexpr_jit_v2.jit-exposed-variable-rexpr. (quote ")
  (print-dup (.exposed-name j) w)
  (.write w " ))"))

(defmethod print-method jit-exposed-variable-rexpr [^jit-exposed-variable-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))


(defrecord jit-hidden-variable-rexpr [hidden-name]
  ;; if there is a variable which is projected out, but still used by one of our
  ;; holes.  Then that variable is a hidden variable as the name of the variable
  ;; could change depending on the hole, but it is still not exposed out
  RexprValueVariable
  (get-value [this] (???))
  (get-value-in-context [this ctx] (???))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] (???))
  (is-bound-in-context? [this ctx])
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx] this)
  Object
  (toString [this] (str "(jit-hidden-variable-rexpr " hidden-name ")")))

(defmethod print-dup jit-hidden-variable-rexpr [^jit-hidden-variable-rexpr j ^java.io.Writer w]
  (.write w "(dyna.rexpr_jit_v2.jit-hidden-variable-rexpr. (quote ")
  (print-dup (.hidden-name j) w)
  (.write w " ))"))

;; the iterables should be something like which variables and their orders can be
(def-base-rexpr jit-placeholder [:unchecked external-name ;; non-nil if accessed via the passed in rexpr
                                 :unchecked local-name ;; if partially rewritten, and now held in a local variable, then non-nil
                                 :var-list placeholder-vars
                                 ]
  #_(exposed-variables [this]
                       (set (map ->jit-placeholder-variable-rexpr (filter is-variable? (vals placeholder-vars)))))
  (rexpr-jittype-hash [this] 0) ;; the jit placeholder most likely goes in the place of a disjunct, so we want to use the same hash-code for this as disjuncts

  )

(def-base-rexpr aggregator-op-partial-result [:var partial-var
                                              :var-list group-vars
                                              :rexpr remains])

(def-base-rexpr jit-run-iterator [:diterator iterator
                                  :var-list iterator-order
                                  :unchecked iterator-variables-bound
                                  :rexpr body]
  (exposed-variables [this] (union (exposed-variables body)
                                   (set iterator-order)
                                   (when (is-variable? iterator)
                                     #{iterator}))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- convert-to-primitive-rexpr [rexpr]
  ;; Not 100% sure if this method is really needed anymore, it seems like is essentially doing nothing
  (cond
    (is-jit-placeholder? rexpr) (let []
                                  (if-not (nil?  (:external-name rexpr))
                                    rexpr ;; this is already a placeholder, so this just gets returned
                                    (make-jit-placeholder (gensym 'jr) nil (:placeholder-vars rexpr))))
    (is-disjunct? rexpr) (let []
                           ;; this is already a primitive, so we can just continue to
                                        ;(debug-repl "prim disjunct")
                           (rewrite-rexpr-children-no-simp rexpr convert-to-primitive-rexpr))
    (or (is-disjunct-op? rexpr) (is-user-call? rexpr))
    (let []
      (debug-repl "bad rexpr")
      (throw (IllegalArgumentException. (str "Can not convert " (rexpr-name rexpr) " to primitive for JIT, should have been a hole"))))

    :else (rewrite-rexpr-children-no-simp (primitive-rexpr rexpr) convert-to-primitive-rexpr)))

(defn- get-placeholder-rexprs [hidden-variables rexpr]
  (if (is-jit-placeholder? rexpr)
    [[rexpr (intersection hidden-variables (exposed-variables rexpr))]]
    (let [sig (@rexpr-containers-signature (rexpr-name rexpr))
          lhidden (if (is-aggregator-op-inner? rexpr)
                    (cons (:incoming rexpr) (:projected rexpr))
                    (for [[[typ _] var] (zipseq sig (get-arguments rexpr))
                          :when (#{:hidden-var} typ)]
                      var))
          hidden-variables (union hidden-variables lhidden)]
      (for [c (get-children rexpr)
            z (get-placeholder-rexprs hidden-variables c)]
        z))))

(defn- primitive-rexpr-cljcode
  ([varmap rexpr]
   (primitive-rexpr-cljcode varmap rexpr :rexpr))
  ([varmap rexpr typ]
   (cond (rexpr? rexpr)
         (cond (is-proj? rexpr) (let [new-var (gensym 'projvar)]
                                  `(let [~new-var (make-variable (Object.))]
                                     (make-no-simp-proj ~new-var ~(primitive-rexpr-cljcode (assoc varmap (:var rexpr) new-var) (:body rexpr)))))
               (is-aggregator-op-inner? rexpr) (if (and (instance? RexprValueVariableForceExposed (:incoming rexpr)) (contains? varmap (:incoming rexpr)))
                                                 (let [new-projs (vec (for [_ (:projected rexpr)]
                                                                        (gensym 'aggproj)))
                                                       new-varmap (merge varmap
                                                                         (zipmap (:projected rexpr) new-projs))
                                                       body (primitive-rexpr-cljcode new-varmap (:body rexpr))
                                                       ret `(let [~@(apply concat (for [v new-projs]
                                                                                    [v `(make-variable (Object.))]))]
                                                              (make-no-simp-aggregator-op-inner
                                                               ~(primitive-rexpr-cljcode new-varmap (:operator rexpr) :unchecked)
                                                               ~(primitive-rexpr-cljcode new-varmap (:incoming rexpr) :var)
                                                               [~@new-projs]
                                                               ~body))]
                                                   ret)
                                                 (let [new-incoming (gensym 'aggin)
                                                       new-projs (vec (for [_ (:projected rexpr)]
                                                                        (gensym 'aggproj)))
                                                       new-varmap (merge varmap
                                                                         {(:incoming rexpr) new-incoming}
                                                                         (zipmap (:projected rexpr) new-projs))
                                                       body (primitive-rexpr-cljcode new-varmap (:body rexpr))
                                                       ret
                                                       `(let [~new-incoming (make-variable (Object.))
                                                              ~@(apply concat (for [v new-projs]
                                                                                [v `(make-variable (Object.))]))]
                                                          (make-no-simp-aggregator-op-inner
                                                           ~(primitive-rexpr-cljcode new-varmap (:operator rexpr) :unchecked)
                                                           ~new-incoming
                                                           [~@new-projs]
                                                           ~body))]
                                                   ret))

               (is-jit-placeholder? rexpr) (let []
                                             ;; this is generating the primitive code for the current R-expr
                                             ;; there should be no local-name, as that would mean that it has some other expression
                                             (assert (:external-name rexpr))
                                             (:external-name rexpr))


               :else (let [rname (rexpr-name rexpr)
                           sig (@rexpr-containers-signature rname)]
                       `(~(symbol "dyna.rexpr-constructors" (str "make-no-simp-" rname))
                         ~@(map #(primitive-rexpr-cljcode varmap %1 (first %2)) (get-arguments rexpr) sig))))
         (is-constant? rexpr) rexpr
         (is-variable? rexpr) (strict-get varmap rexpr)
         (= typ :rexpr-list) (into [] (map #(primitive-rexpr-cljcode varmap % :rexpr) rexpr))
         (= typ :var-list) (into [] (map #(primitive-rexpr-cljcode varmap % :var) rexpr))
         (= typ :var-map) (into {} (for [[k var] rexpr]
                                     [k (primitive-rexpr-cljcode varmap var :var)]))
         (instance? Aggregator rexpr) (with-meta (symbol "dyna.rexpr-aggregators" (str "defined-aggregator-" (:name rexpr)))
                                        {:tag "dyna.rexpr_aggregators.Aggregator"})
         ;`(get @dyna.rexpr-aggregators/aggregators ~(:name rexpr)) ;; this is a object which is reference, hence we can not embed it in the code directlty, and instead will use this to look up the aggregator

         (nil? rexpr) nil
         (#{:str :file-name :mult :unchecked} typ) rexpr
         :else (do
                 (debug-repl "unknown mapping to constructor")
                 (???)))))

(defn- primitive-rexpr-with-placeholders [rexpr new-arg-names]
  (let [rf (fn rf [typ v args]
             (cond (and (= typ :rexpr) (rexpr? v))
                   (cond (is-proj? v)
                         (let [vv (:var v)]
                           (assert (not (instance? jit-exposed-variable-rexpr vv)))
                           (if (or (instance? jit-local-variable-rexpr vv)
                                   (instance? jit-hidden-variable-rexpr vv))
                             (make-no-simp-proj vv (rf :rexpr (:body v) args))
                             (let [n (jit-local-variable-rexpr. (gensym 'projvar))
                                   a (assoc args (:var v) n)
                                   bb (rf :rexpr (:body v) a)]
                               (dyna-assert (contains? (exposed-variables bb) n))
                               (make-no-simp-proj n bb))))

                         (is-aggregator-op-inner? v)
                         (let [incoming (:incoming v)
                               proj-out (:projected v)
                               new-args (loop [a args
                                               vs (if (and (instance? RexprValueVariableForceExposed incoming) (contains? new-arg-names incoming))
                                                    proj-out
                                                    (cons incoming proj-out))]
                                          (if (empty? vs)
                                            a
                                            (let [vv (first vs)]
                                              (if (or (instance? jit-local-variable-rexpr vv)
                                                      (instance? jit-hidden-variable-rexpr vv))
                                                (recur a (rest vs))
                                                (let [lvar (jit-local-variable-rexpr. (gensym 'aggprojvar))]
                                                  (recur (assoc a vv lvar)
                                                         (rest vs)))))))
                               body (rf :rexpr (:body v) new-args)
                               ret (make-no-simp-aggregator-op-inner (:operator v)
                                                                     (get new-args incoming incoming)
                                                                     (vec (map #(get new-args % %) proj-out))
                                                                     body)
                               ]
                           ret)

                         (is-jit-placeholder? v)
                         (let []
                           ;; we just need to rename the variables, otherwise this should just stay the same
                           (remap-variables v args))

                         :else (rewrite-all-args v #(rf %1 %2 args)))

                   (= typ :rexpr-list) (into [] (map #(rf :rexpr % args) v))
                   (= typ :var-list) (into [] (map #(rf :var % args) v))
                   (= typ :var-map) (into {} (for [[k var] v]
                                               [k (rf :var var args)]))


                   (#{:str :unchecked :file-name :mult} typ) (let []
                                                               (assert (and (not (rexpr? v))
                                                                            (not (instance? RexprValue v))))
                                                               v)

                   (or (instance? jit-exposed-variable-rexpr v)
                       (instance? jit-local-variable-rexpr v)
                       (instance? jit-hidden-variable-rexpr v)
                       ;(instance? jit-expression-variable-rexpr v)
                       (is-constant? v)
                       ) v ;; no change

                   (instance? RexprValue v) (strict-get args v)

                   :else (do
                           (debug-repl "unknown placeholder expression qwerwqer")
                           (???))))]
    (rf :rexpr rexpr (into {} (for [[k v] new-arg-names]
                                [k (jit-exposed-variable-rexpr. v)])))))

(declare ^{:private true}
         generate-conversion-function-matcher
         generate-unordered-list-matcher)

(defn- generate-unordered-list-matcher [matching-against-var
                                        matching-value
                                        values-to-vars
                                        inner-function]
  (case (count matching-value)
    0 (inner-function values-to-vars)
    1 (let [elemv (gensym 'elemv)]
        `(let [~elemv (first ~matching-against-var)]
           ~(generate-conversion-function-matcher elemv
                                                  (first matching-value)
                                                  values-to-vars
                                                  inner-function)))
    (let [elemv (gensym 'elemv)
          otherv (gensym 'otherv)]
      `(for [[~elemv ~otherv] (subselect-list ~matching-against-var)
             ret# ~(generate-conversion-function-matcher elemv
                                                         (first matching-value)
                                                         values-to-vars
                                                         (fn [values-to-vars]
                                                           (generate-unordered-list-matcher otherv
                                                                                            (rest matching-value)
                                                                                            values-to-vars
                                                                                            inner-function)))]
         ret#))))

(defn- generate-ordered-list-matcher [matching-against-var
                                      matching-value
                                      values-to-vars
                                      inner-function]
  (if (= 0 (count matching-value))
    (inner-function values-to-vars)
    ((fn rec [a i values-to-vars]
       (if (empty? a)
         (inner-function values-to-vars)
         (generate-conversion-function-matcher
          `(nth ~matching-against-var ~i)
          (first a)
          values-to-vars
          #(rec (rest a) (+ i 1) %))))
     (seq matching-value) 0 values-to-vars)))


(defn- generate-conversion-function-matcher [matching-against-var
                                             matching-value
                                             values-to-vars
                                             inner-function]
  (cond
    (or (is-conjunct? matching-value)
        (is-disjunct? matching-value))
    (let [argv (gensym 'argv)]
      `(when (~(if (is-conjunct? matching-value) 'is-conjunct? 'is-disjunct?) ~matching-against-var)
         (let [~argv (. ~(with-meta matching-against-var {:tag (type matching-value)}) ~'args)]
           (when (= (count ~argv) ~(count (:args matching-value)))
             ~(generate-unordered-list-matcher argv
                                               (:args matching-value)
                                               values-to-vars
                                               inner-function)))))

    (is-jit-placeholder? matching-value)
    (let [values-to-vars (assoc values-to-vars matching-value matching-against-var)
          exposed (gensym 'exposed)]
      ;; the matching against the local R-expr should maybe happen first, and then it could do additional matching against anything which is a jit placeholder
      ;; this will have that the number of variables which are in the placeholder will identify some of the different values here?  But if there is something which
      `(let [~exposed (vec (exposed-variables ~matching-against-var))]
         ;; though this is a set, so the set could be smaller if there are fewer exposed variables, or something is aliased together
         ;; though in that case, it might
         (when (= (count ~exposed) ~(count (:placeholder-vars matching-value)))
           ~(generate-unordered-list-matcher exposed
                                             (:placeholder-vars matching-value)
                                             values-to-vars
                                             inner-function))))

    (is-constant? matching-value)
    (let [cval (get-value matching-value)]
      (assert (not (symbol? cval)))
      `(when (= (get-value ~matching-against-var) ~(get-value matching-value))
         ~(inner-function values-to-vars)))

    (is-variable? matching-value)
    (if (contains? values-to-vars matching-value)
      `(when (= ~(strict-get values-to-vars matching-value) ~matching-against-var) ;; I suppose that this could consider the current value
         ~(inner-function values-to-vars))
      (inner-function (assoc values-to-vars
                             matching-value matching-against-var)))

    (instance? Aggregator matching-value)
    `(when (= (. ~(with-meta matching-against-var {:tag Aggregator}) ~'name) ~(.name ^Aggregator matching-value))
       ~(inner-function values-to-vars))

    (is-aggregator-op-inner? matching-value)
    (let [operator (gensym 'operator)
          incoming (gensym 'incoming)
          projected (gensym 'projected)
          body (gensym 'body)]
      `(when (is-aggregator-op-inner? ~matching-against-var)
         (let [~operator (. ~(with-meta matching-against-var {:tag aggregator-op-inner-rexpr}) ~'operator)
               ~incoming (. ~(with-meta matching-against-var {:tag aggregator-op-inner-rexpr}) ~'incoming)
               ~projected (. ~(with-meta matching-against-var {:tag aggregator-op-inner-rexpr}) ~'projected)
               ~body (. ~(with-meta matching-against-var {:tag aggregator-op-inner-rexpr}) ~'body)]
           ~(generate-conversion-function-matcher
             operator
             (:operator matching-value)
             values-to-vars
             (fn [values-to-vars]
               (generate-conversion-function-matcher
                incoming
                (:incoming matching-value)
                values-to-vars
                (fn [values-to-vars]
                  ;; match against the number of projected variables, then the body of the aggregator, and then the order in which projected
                  ;; variables are aligned.  The alignment of the projected variables does not matter that much and it is the locations in the body
                  ;; of the aggregator which are going to be the elements that matter here
                  `(when (= (count ~projected) ~(count (:projected matching-value)))
                     ~(generate-conversion-function-matcher
                       body
                       (:body matching-value)
                       values-to-vars
                       (fn [values-to-vars]
                         (generate-unordered-list-matcher projected
                                                          (:projected matching-value)
                                                          values-to-vars
                                                          inner-function)))))))))))

    (rexpr? matching-value)
    (let [rtype (rexpr-name matching-value)
          rexpr-sig (get @rexpr-containers-signature rtype)
          rcname (strict-get @rexpr-containers-class-name rtype)
          var-expands (for [[typ name] rexpr-sig
                            :let [gvar (gensym name)]]
                        {:cur-value ((keyword name) matching-value)
                         :var gvar
                         :type typ
                         :let-expr [gvar (list '.
                                               (with-meta matching-against-var {:tag rcname})
                                               (symbol (munge name)))]})
          body-fn (fn br [check-against values-to-vars]
                    (if (empty? check-against)
                      (inner-function values-to-vars)
                      (let [f (first check-against)
                            r (rest check-against)]
                        #_(when (and (not (rexpr? (:cur-value f)))
                                     (not (is-rexpr-value? (:cur-value f)))
                                     (not (is-aggregator-op-outer? matching-value))
                                     )
                            (debug-repl "bad type"))
                        (cond (or (#{:mult :file-name :boolean :str} (:type f))
                                  (and (= :unchecked (:type f)) (vector? (:cur-value f))))
                          `(when (= ~(:cur-value f) ~(:var f))
                             ;(println ~(str "matched value " (:cur-value f)))
                             ~(br r values-to-vars))

                          (#{:var-list} (:type f))
                          (generate-ordered-list-matcher (:var f) (:cur-value f) values-to-vars (partial br r))

                          :else
                          (do
                            #_(when (vector? (:cur-value f))
                              (debug-repl "bad"))
                            (generate-conversion-function-matcher (:var f)
                                                                  (:cur-value f)
                                                                  values-to-vars
                                                                  (partial br r)))))))]
      `(when (~(symbol "dyna.rexpr-constructors" (str "is-" (rexpr-name matching-value) "?")) ~matching-against-var)
         ;(println ~(str "matched " (rexpr-name matching-value)))
         (let [~@(apply concat (map :let-expr var-expands))]
           ~(body-fn var-expands values-to-vars))))

    :else
    (do
      (debug-repl "no match")
      (???))))


(declare ^:private find-iterators-cljcode)

(defn- synthize-rexpr-cljcode [rexpr]
  ;; this should just generate the required clojure code to convert the rexpr
  ;; (argument) into a single synthic R-expr.  This is not going to evaluate the code and do the conversion
  (let [prim-rexpr (convert-to-primitive-rexpr rexpr)
        exposed-vars (set (filter is-variable? (exposed-variables prim-rexpr)))
        placeholder-rexprs (set (get-placeholder-rexprs #{} prim-rexpr))
        root-rexpr (gensym 'root) ;; the variable which will be the argument for the conversions
                                        ;vars-path (get-variables-and-path rexpr)
                                        ;[var-access var-gen-code] (get-variables-values-letexpr root-rexpr (keys vars-path)) ;; this might have to handle exceptions which are going to thrown by the
        new-rexpr-name (gensym 'jit-rexpr)
        new-arg-names (merge (into {} (map (fn [v] [v (gensym 'jv)]) exposed-vars))
                             (into {} (map (fn [r]
                                             (dyna-assert (:external-name r))
                                             [r (:external-name r)]) (map first placeholder-rexprs)))
                             (into {} (for [[_ vs] placeholder-rexprs
                                            v vs]
                                        [{:hidden-var v} (gensym 'jhv)])))
        new-arg-names-rev (into {} (for [[k v] new-arg-names]
                                     [v k]))
        new-arg-order (vec (vals new-arg-names))
        jittype-hash (rexpr-jittype-hash prim-rexpr)
        prim-rexpr-with-placeholder (primitive-rexpr-with-placeholders prim-rexpr new-arg-names)
        find-iterator-code (binding [*jit-generating-rewrite-for-rexpr* (str "dyna.rexpr_jit_v2." new-rexpr-name "-rexpr")
                                     *local-variable-names-for-variable-values* (volatile! nil)
                                     ]
                             (find-iterators-cljcode prim-rexpr-with-placeholder))
        rexpr-def-expr `(do (def-base-rexpr ~new-rexpr-name [~@(flatten (for [a new-arg-order
                                                                              :let [v (get new-arg-names-rev a)]]
                                                                          (cond (rexpr? v) [:rexpr a]
                                                                                (is-variable? v) [:var a]
                                                                                (:hidden-var v) [:hidden-var a]
                                                                                :else (do (debug-repl "???")
                                                                                          (???)))
                                                                          ))]
                              ;; should there be some override for the get method
                              ;; such that we can get the fields on the origional
                              ;; expression?  But in the case that there
                              (~'rexpr-jit-info ~'[this]
                               (get @dyna.rexpr-jit-v2/rexprs-types-constructed (quote ~new-rexpr-name)))

                              (~'primitive-rexpr ~'[this]
                               ~(primitive-rexpr-cljcode new-arg-names prim-rexpr))
                              (~'rexpr-jittype-hash [this] ~jittype-hash))
                            (defmethod rexpr-printer ~(symbol (str new-rexpr-name "-rexpr")) ~'[r]
                              (rexpr-printer (primitive-rexpr ~'r))))
        conversion-function-expr `(fn [~root-rexpr]
                                    (first
                                     ~(generate-conversion-function-matcher root-rexpr
                                                                            prim-rexpr
                                                                            {}
                                                                            (fn [values-to-vars]
                                                                              `(list ;; return a list, as we are getting the first element from the iterator
                                                                                (if (tlocal recursive-transformation-to-jit-state)
                                                                                  (~(symbol (str "make-" new-rexpr-name))
                                                                                   ~@(for [a new-arg-order
                                                                                           :let [v (strict-get new-arg-names-rev a)]]
                                                                                       (cond (rexpr? v) `(convert-to-jitted-rexpr-fn ~(strict-get values-to-vars v))
                                                                                             (and (map? v) (:hidden-var v)) (strict-get values-to-vars (:hidden-var v))
                                                                                             :else (strict-get values-to-vars v))))
                                                                                  (~(symbol (str "make-" new-rexpr-name))
                                                                                   ~@(for [a new-arg-order
                                                                                           :let [v (strict-get new-arg-names-rev a)]]
                                                                                       (if (and (map? v) (:hidden-var v))
                                                                                         (strict-get values-to-vars (:hidden-var v))
                                                                                         (strict-get values-to-vars v))))))))))
        def-iterator-expr (when find-iterator-code
                            `(swap! rexpr-iterators-accessors update ~(symbol (str new-rexpr-name "-rexpr")) conj
                                    (fn [~(with-meta 'rexpr {:tag (str "dyna.rexpr_jit_v2." new-rexpr-name "-rexpr")})]
                                      (let [^RContext ~'**context** (ContextHandle/get)
                                            ^ThreadVar ~'**threadvar** (ThreadVar/get)]
                                        ~find-iterator-code))))
        ret {:orig-rexpr rexpr
             :prim-rexpr prim-rexpr
             :generated-name new-rexpr-name
             :make-rexpr-type rexpr-def-expr
             :def-iterator-expr def-iterator-expr
             :conversion-function-expr conversion-function-expr
                                        ;:variable-name-mapping new-arg-names ;; map from existing-name -> new jit-name
             :variable-name-mapping-rev new-arg-names-rev
             :variable-order new-arg-order ;; the order of jit-names as saved in the R-expr
             :prim-rexpr-placeholders  prim-rexpr-with-placeholder
             ;; ;; should the conversion function have that there is some expression.  In the case that it might result in some of
             ;; ;; if there is something which is giong to construct this value, though there might
             ;; :conversion-function-args (fn [& args] (???))

             ;; ;; check that the shape of the R-expr matches the kind of the thing that we can convert into this generated code
             ;; :check-could-be-converted (fn [rexpr] (???))
             }]
    (swap! rexprs-types-constructed assoc new-rexpr-name ret)
    ret))

(defn- convert-to-existing-jit-type [rexpr]
  (first (for [converter (get @rexpr-map-to-jit-hash-group (rexpr-jittype-hash rexpr))
               :let [c ((:conversion-function converter) rexpr)]
               :when (not (nil? c))]
           c)))

(declare ^:private converter-matching-rexpr)

(defn- converter-matching-unordered-list [rtype-list rexpr matched-so-far]
  (when (= (count rtype-list) (count rexpr))
    (case (count rtype-list)
      0 (list nil) ;; there is nothing in the list to match
      1 (converter-matching-rexpr (first rtype-list) (first rexpr) matched-so-far)
      ((fn rec [la lb mm]
         (if (empty? la)
           (list nil)
           (let [rb (rest lb)]
             (for [[item idx] (zipseq la (range))
                   l1 (converter-matching-rexpr item (first lb) matched-so-far)
                   l2 (rec (drop-nth la idx) rb (merge matched-so-far l1))]
               (merge l1 l2)))))
       rtype-list rexpr matched-so-far))))

(defn- converter-matching-ordered-list [rtype-list rexpr matched-so-far]
  (when (= (count rtype-list) (count rexpr))
    (if (= 0 (count rtype-list))
      (list nil)
      (for [l1 (converter-matching-rexpr (first rtype-list) (first rexpr) matched-so-far)
            l2 (converter-matching-ordered-list (rest rtype-list) (rest rexpr) (merge matched-so-far l1))]
        (merge l1 l2)))))

(defn- converter-matching-rexpr [rtype-rexpr rexpr matched-so-far]
  (cond (or (and (rexpr? rtype-rexpr) (= (type  rexpr) (type rtype-rexpr)))
            (and (is-rexpr-value? rtype-rexpr) (is-rexpr-value? rexpr)))
        (cond (or (is-disjunct? rtype-rexpr)
                  (is-conjunct? rtype-rexpr))
              (let [rtype-args (:args rtype-rexpr)
                    args (:args rexpr)]
                (converter-matching-unordered-list rtype-args args matched-so-far))

              (is-jit-placeholder? rtype-rexpr)
              (list {rtype-rexpr rexpr})

              (or (instance? jit-exposed-variable-rexpr rtype-rexpr)
                  (instance? jit-local-variable-rexpr rtype-rexpr))
              (if (contains? matched-so-far rtype-rexpr)
                (when (= (get matched-so-far rtype-rexpr) rexpr)
                  (list nil)) ;; check if this is the same variable getting matched in both cases
                (list {rtype-rexpr rexpr}))

              (is-constant? rtype-rexpr)
              (when (and (is-constant? rexpr)
                         (= (get-value rtype-rexpr) (get-value rexpr)))
                (list nil))

              (is-aggregator-op-inner? rtype-rexpr)
              (when (and (= (:operator rtype-rexpr) (:operator rexpr)))
                (for [l1 (converter-matching-rexpr (:incoming rtype-rexpr) (:incoming rexpr) matched-so-far)
                      l2 (converter-matching-rexpr (:body rtype-rexpr) (:body rexpr) (merge matched-so-far l1))
                      l3 (converter-matching-unordered-list (:projected rtype-rexpr) (:projected rexpr) (merge matched-so-far l1 l2))]
                  (merge l1 l2 l3)))

              (rexpr? rtype-rexpr)
              ((fn rec [rtype-args args matched-so-far]
                           (if (empty? rtype-args)
                             (list nil)
                             (for [l1 (if (vector? (first rtype-args))
                                        (converter-matching-ordered-list (first rtype-args) (first args) matched-so-far)
                                        (converter-matching-rexpr (first rtype-args) (first args) matched-so-far))
                                   l2 (rec (rest rtype-args) (rest args) (merge matched-so-far l1))]
                               (merge l1 l2))))
                         (get-arguments rtype-rexpr)
                         (get-arguments rexpr)
                         matched-so-far)

              :else
              (do
                (debug-repl "converter matcher other type")
                (???)))

        (or (instance? Aggregator rtype-rexpr)
            (string? rtype-rexpr)
            (int? rtype-rexpr)
            (boolean? rtype-rexpr)
            (instance? java.net.URL rtype-rexpr))
        (when (= rtype-rexpr rexpr) (list nil))

        ))

(defn- compute-converter-matching [rtype rexpr]
  (let [prim-rexpr (:prim-rexpr-placeholders rtype)
        new-mapping (first (converter-matching-rexpr prim-rexpr rexpr {}))]
    (when-not (nil? new-mapping)
      (assoc rtype :variable-name-mapping-rev
             (into {} (for [[a b] new-mapping]
                        (cond (instance? jit-exposed-variable-rexpr a)
                              [(:exposed-name a) b]
                              (is-jit-placeholder? a)
                              [(:external-name a) b]
                              (instance? jit-local-variable-rexpr a)
                              (do
                                ;; this does not have a conversion between these variables as they are not exposed
                                (assert (instance? jit-local-variable-rexpr b))
                                nil)
                              :else (do
                                      (debug-repl "convert matching???")
                                      (???)))))))))

(defn- synthize-rexpr [rexpr]
  ;; this will identify if an R-expr already has a type which is synthized, and either return that type/conversion function
  (if (is-jit-placeholder? rexpr)
    (let []
      (debug-repl "synth hole")
      (???))
    (let [jittype-hash (rexpr-jittype-hash rexpr)
          rtype (let [vv (volatile! nil)]
                  ;; bit odd to have this under the swap!, as it is going to potentially cause this transform to happen multiple times if there are racing threads
                  ;; which might not be the best....
                  (swap! rexpr-map-to-jit-hash-group
                         (fn [x]
                           (let [converters (get x jittype-hash)
                                 matches (first
                                          (for [cc converters
                                                :let [mc (compute-converter-matching cc rexpr)]
                                                :when (not (nil? mc))]
                                            mc))]
                             #_(when (and (not (empty? converters)) (nil? matches))
                                 (debug-repl "jit type same, but matched"))
                             (if-not (nil? matches)
                               (do
                                 (vreset! vv matches)
                                 x)
                               (let [new-generated (synthize-rexpr-cljcode rexpr)
                                     ;; we need to create a new converter and add it to the list
                                     convert-function (try
                                                        (binding [*ns* dummy-namespace]
                                                          (eval `(do
                                                                   (ns dyna.rexpr-jit-v2)
                                                                   ~(:make-rexpr-type new-generated)
                                                                   ~(:def-iterator-expr new-generated)
                                                                   ~(:conversion-function-expr new-generated))))
                                                        (catch Exception err (do
                                                                               (println "FAILED TO GENERATE CODE")
                                                                               (aprint new-generated)
                                                                               (debug-repl "convert fn" false)
                                                                               (throw err))))
                                     matches (assoc new-generated :conversion-function convert-function)]
                                 (vreset! vv matches)
                                 (assoc x jittype-hash (cons matches converters)))))))
                  @vv)
          ret ((:conversion-function rtype) rexpr)]
      (dyna-assert (not (nil? ret)))
      [ret rtype])))

(declare ^:private convert-to-jitted-rexpr-fn)

(defn- convert-to-jitted-rexpr-inspect [rexpr]
  ;; look at the type of the primitive R-expr and figure out if we need to transform some of the sub units
  (context/bind-no-context
   (tbinding [use-optimized-disjunct false]
             (let [jinfo (rexpr-jit-info rexpr)]
               (cond (contains? jinfo :generated-name) rexpr ;; this is already a jit compiled type.  There is nothing to do here.  Though I suppose that we could map its arguments?

                     (is-aggregator? rexpr) (convert-to-jitted-rexpr-fn
                                             (convert-basic-aggregator-to-op-aggregator rexpr))

                     (is-user-call? rexpr) rexpr ;; there is nothing that we can do for this

                     ;; figure out if this is a big disjunct or a small disjunct.  If it is a big disjunct, then it would become a hole with its sub units getting converted
                     ;; if this is a small disjunct, then we can convert it to a primitive R-expr type, and then JIT compile that
                     (is-disjunct-op? rexpr)
                     (let [trie (:rexprs rexpr)
                           vars (:disjunction-variables rexpr)
                           elems (take 11 (trie/trie-get-values trie nil))
                           all-ground (every? (fn [z] (every? #(not (nil? %)) z)) (map first elems))]
                       (if (> (count elems) 8)
                         ;; then we are going to rewrite the leafs of the R-exprs
                         (rewrite-rexpr-children rexpr convert-to-jitted-rexpr-fn)
                         (let [new-disjunct (vec (for [[vals rx] elems
                                                       :let [vals-r (vec (for [[val var] (zipseq vals vars)
                                                                               :when (not (nil? val))]
                                                                           (make-no-simp-unify var (make-constant val))))]]
                                                   (make-conjunct (conj vals-r rx))))
                               ret (make-no-simp-disjunct new-disjunct)]
                           (convert-to-jitted-rexpr-fn ret))))


                     ;; This R-expr can be converted into the JIT, but it might have things inside of the R-expr which will need to get removed
                     ;; these things will have to get identified and converted into holes
                     :else
                     (let [pl (volatile! {}) ;; things go into holes
                           rp (fn rr [rexpr]
                                (let [jinfo (rexpr-jit-info rexpr)]
                                  (if-not (:jittable jinfo true)
                                    (cond (is-aggregator? rexpr) (rr (convert-basic-aggregator-to-op-aggregator rexpr))
                                          (is-disjunct-op? rexpr)
                                          (let [trie (:rexprs rexpr)
                                                vars (:disjunction-variables rexpr)
                                                elems (take 11 (trie/trie-get-values trie nil))
                                                all-ground (every? (fn [z] (every? #(not (nil? %)) z)) (map first elems))]
                                            (if (> (count elems) 8)
                                              (let [id (gensym 'jr)
                                                    exposed (exposed-variables rexpr)
                                                    new-disjunct (if (tlocal recursive-transformation-to-jit-state)
                                                                   (rewrite-rexpr-children rexpr convert-to-jitted-rexpr-fn)
                                                                   rexpr)]
                                                (vswap! pl assoc id new-disjunct)
                                                (make-jit-placeholder id nil (vec exposed)))
                                              (let [new-disjunct (vec (for [[vals rx] elems
                                                                            :let [vals-r (vec (for [[val var] (zipseq vals vars)
                                                                                                    :when (not (nil? val))]
                                                                                                (make-no-simp-unify var (make-constant val))))]]
                                                                        (make-conjunct (conj vals-r
                                                                                             (rr rx)))))
                                                    ret (make-no-simp-disjunct new-disjunct)]
                                                ret)))
                                          :else
                                          (let [id (gensym 'jr)
                                                exposed (exposed-variables rexpr)]
                                            (vswap! pl assoc id rexpr)
                                            (make-jit-placeholder id nil (vec exposed))))
                                    (rewrite-rexpr-children rexpr rr))))
                           nr (rp rexpr)
                           ;; QUESTION: should this always synthize or should there be something which will stop it.
                           ;; if we allow for merging of jitted types, then it would have that there is some expression between
                           ;; them.  But how would it allow for the different states to be encoded
                           ;;
                           ;; When this figures out which of the states are encoded, it will
                           vvvv (when (is-jit-placeholder? nr)
                                  (debug-repl "placeholder fail"))
                           [synthed _] (synthize-rexpr nr)]
                       (if-not (empty? @pl)
                         (rewrite-rexpr-children synthed (fn [r]
                                                           (assert (is-jit-placeholder? r))
                                                           (strict-get @pl (:external-name r))))
                         synthed)))))))

(defn- convert-to-jitted-rexpr-fn [rexpr]
  (if (or (not (tlocal system/generate-new-jit-states))
          (is-jit-placeholder? rexpr) ;; already a placeholder, nothing else to do
          (contains? (rexpr-jit-info rexpr) :generated-name) ;; already jitted
          (is-user-call? rexpr) ;; nothing can do for this
          )
    rexpr ;; just return the R-expr unmodified in this case,
    (let [existing-type (convert-to-existing-jit-type rexpr)]
      (if-not (nil? existing-type)
        existing-type ;; then there was some existing type which was able to do the conversion, so we did not have to worry about it
        (convert-to-jitted-rexpr-inspect rexpr)))))


(intern 'dyna.rexpr-constructors 'convert-to-jitted-rexpr convert-to-jitted-rexpr-fn)

(defn- get-matchers-for-value [val]
  (into [] (map first (filter (fn [[name func]] (func val)) @rexpr-matchers))))

(def ^:private free-variable-matchers (delay (get-matchers-for-value (make-variable (Object.)))))
(def ^:private ground-variable-matchers (delay (get-matchers-for-value (make-constant (Object.)))))



(defn- is-composit-rexpr? [rexpr]
  ;; meaning that there is some sub-rexprs here, in which case, we might want to constructed
  (or (is-conjunct? rexpr) (is-disjunct? rexpr) (is-disjunct-op? rexpr) (is-proj? rexpr)
      (is-aggregator? rexpr) (is-aggregator-op-outer? rexpr) (is-aggregator-op-inner? rexpr)
      (some (fn r [x] (or (rexpr? x)
                          (and (seqable? x) (some r x))))
            (get-arguments rexpr))))



(defn jit-metadata
  ([rexpr]
   (let [r (get @*jit-rexpr-rewrite-metadata* rexpr)]
     (if (nil? r)
       (get (vswap! *jit-rexpr-rewrite-metadata* assoc rexpr (volatile! {})) rexpr)
       r)))
  ([] (jit-metadata *jit-currently-rewriting*)))

(defn- generate-cljcode [generate-functions]
  (if (empty? generate-functions)
    (fn [f] (f))
    (let [f (first generate-functions)
          r (generate-cljcode (rest generate-functions))]
      (fn [inner] (f (partial r inner))))))

(defn- can-generate-code? []
  (and (not (nil? *jit-generate-functions*))
       (not= () *jit-generate-functions*)))

(defn- add-to-generation! [value]
  (cond (fn? value)
        (when-not (nil? *jit-generate-functions*)
          (conj! *jit-generate-functions* value))

        (= :void (:type value)) nil

        :else
        (let [cljcode (if (and (map? value) (contains? value :cljcode-expr))
                        (:cljcode-expr value)
                        value)]
          (dyna-assert (not (nil? cljcode)))
          (when-not (nil? cljcode)
            (add-to-generation! (fn [inner]
                                  `(do
                                     ~cljcode
                                     ~(inner))))))))

(defn- generate-cljcode-to-materalize-rexpr [rexpr & {:keys [simplify-result attempt-variable-read-values] :or {simplify-result false attempt-variable-read-values false}}]
  ;; this is going to have to figure out which variables are referencing some value
  ;; and then create a new R-expr type with holes, and generate the new "make R-expr"

  ;; if simplify result is true, then we should pass the expression to simplify
  ;; again.  This will allow for checkpoints to keep rewriting from its
  ;; seralized state, whereas for an ending state, we might just want to return
  ;; it, as it should go back into the control flow of "other" stuff
  (cond (is-empty-rexpr? rexpr)
        {:type :rexpr
         :rexpr-type rexpr
         :cljcode-expr `(make-multiplicity 0)} ;; we can not throw here as there are multiple nested try-caches which could catch it by accident, so return 0
        (is-jit-placeholder? rexpr)
        (if (:external-name rexpr)
          {:type :rexpr
           :rexpr-type ((keyword (:external-name rexpr)) *jit-generating-rewrite-for-rexpr*)
           :cljcode-expr `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                             ~(:external-name rexpr))}
          {:type :rexpr
           :rexpr-type (strict-get @(jit-metadata rexpr) :current-rexpr)
           :cljcode-expr (:local-name rexpr)})
        :else
        (let [re (if-not (is-composit-rexpr? rexpr)
                   (let [local-vars-bound @*local-variable-names-for-variable-values*]
                     ;; this is a simple primitive R-expr type (like multiplicity or builtin
                     ;; like add) there is no reason to generate a more complex R-expr type for
                     ;; this.  So we are going to just generate something which generates this type directly
                     {:type :rexpr
                      :rexpr-type rexpr
                      :cljcode-expr `(~(symbol "dyna.rexpr-constructors" (str "make-" (rexpr-name rexpr)))
                                      ~@(doall (for [arg (get-arguments rexpr)]
                                                 (cond (number? arg) arg
                                                       (is-constant? arg) `(make-constant ~(get-value arg))
                                                       (instance? jit-exposed-variable-rexpr arg)
                                                       (if (contains? local-vars-bound arg)
                                                         `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                                                         (let [z `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                                     ~(:exposed-name arg))]
                                                           (if attempt-variable-read-values
                                                             `(get-representation-in-context ~z ~'**context**)
                                                             z)))
                                                       (and (instance? jit-local-variable-rexpr arg) (is-bound-jit? arg))
                                                       `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                                                       (instance? jit-expression-variable-rexpr arg)
                                                       `(constant-value-rexpr. ~(:cljcode arg))
                                                       :else (do (debug-repl "arg type")
                                                                 (???))))))})
                   (let [local-vars-bound @*local-variable-names-for-variable-values*
                         exposed (exposed-variables rexpr)
                         remapped-locals (into {} (for [v exposed
                                                        :when (or (instance? jit-local-variable-rexpr v)
                                                                  (instance? jit-hidden-variable-rexpr v)
                                                                  (instance? jit-exposed-variable-rexpr v)
                                                                  (instance? jit-expression-variable-rexpr v))]
                                                    [v (make-variable (gensym 'vhold))]))
                         new-r (remap-variables rexpr remapped-locals)
                         ;; new-r (remap-variables-func rexpr (fn [var]
                         ;;                                     (if (contains? remapped-locals var)
                         ;;                                       (remapped-l))))
                         [_ new-synth] (synthize-rexpr new-r)
                         ;rlocal-map (into {} (for [[k v] remapped-locals] [v k]))
                         rvarmap (:variable-name-mapping-rev new-synth)
                         hidden-variables (into {} (for [[k v] rvarmap
                                                         :when (and (map? v) (:hidden-var v))]
                                                     [(:hidden-var v) k]))
                         target-r ((:conversion-function new-synth) rexpr)]
                     (dyna-assert (not (nil? target-r))) ;; if this is nil, then that means this is not a matching R-expr
                     {:type :rexpr
                      :rexpr-type target-r
                      :cljcode-expr `(~(symbol "dyna.rexpr-constructors" (str "make-no-simp-" (:generated-name new-synth)))
                                      ~@(doall (for [arg (get-arguments target-r)]
                                                 (cond (instance? jit-exposed-variable-rexpr arg)
                                                       (if (contains? local-vars-bound arg)
                                                         `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                                                         (let [z `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                                     ~(:exposed-name arg))]
                                                           (if attempt-variable-read-values
                                                             `(get-representation-in-context ~z ~'**context**)
                                                             z)))
                                                       (and (instance? jit-local-variable-rexpr arg) (is-bound-jit? arg))
                                                       `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                                                       (instance? jit-expression-variable-rexpr arg)
                                                       `(constant-value-rexpr. ~(:cljcode arg))
                                                       (is-jit-placeholder? arg)
                                                       (let []
                                                         (if (:external-name arg)
                                                           `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                               ~(:external-name arg))
                                                           (do
                                                             (assert (:local-name arg))
                                                             (:local-name arg))))

                                                       (contains? hidden-variables arg)
                                                       `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                           ~(strict-get hidden-variables arg))

                                                       :else (do (debug-repl "arg type")
                                                                 `(bad-gen "bad type generation" ~arg))))))}))]
          (if (and simplify-result (not (is-multiplicity? rexpr)))
            (assoc re :cljcode-expr `(~'simplify ~(:cljcode-expr re)))
            re))))

(defn- add-return-rexpr-checkpoint! [rexpr]
  (let [materalize-code (:cljcode-expr (generate-cljcode-to-materalize-rexpr rexpr :simplify-result true))
        status-counter (and system/status-counters (not @*jit-incremented-status-counter*))]
    (when status-counter (vreset! *jit-incremented-status-counter* true))
    (add-to-generation! (fn [inner]
                          `(try
                             ~(if status-counter
                                `(do (StatusCounters/jit_rewrite_performed) ;; track that we have performed at least 1 rewrite using the JITted code
                                     ~(inner))
                                (inner))
                             (catch DynaJITRuntimeCheckFailed ~'_
                               ~materalize-code))))))

(defn- add-unification-failure-checkpoint! [rexpr]
  (let [materalize-code (:cljcode-expr (generate-cljcode-to-materalize-rexpr rexpr :simplify-result true))] ;; we want to simplify the result here, as this might be some internal branch has failed instead of the whole expression
    (add-to-generation! (fn [inner]
                          `(try
                             ~(inner)
                             (catch UnificationFailure ~'_
                               ~materalize-code))))))

(defn- generate-cljcode-fn [final-rexpr]
  `(fn [~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)}) ~'simplify]
     ~(when system/status-counters `(StatusCounters/match_attempt))
     (let [^RContext ~'**context** (ContextHandle/get)
           ^ThreadVar ~'**threadvar** (ThreadVar/get)]
       (try
         (do ~((generate-cljcode (persistent! *jit-generate-functions*))
               (fn []
                 (:cljcode-expr (generate-cljcode-to-materalize-rexpr final-rexpr))
                 ;; TODO: the inner expression needs to return an R-expr which corresponds with the state of the JITted code after it has performed many steps
                 ;; either this should already be put into the JITted code here, or it should have already been generated somewhere else
                                        ;`(???)
                 )))
         (catch DynaJITRuntimeCheckFailed ~'_ nil)))))

#_(def ^{:private true :dynamic true} *jit-cached-expression-results* nil)

#_(defn- add-to-expression-cache!
  ([expression result]
   (when-not (nil? *jit-cached-expression-results*)
     (assoc! *jit-cached-expression-results* expression result)))
  ([value]
   (add-to-expression-cache! (:cljcode-expr value) value)))

#_(defn- add-precondition-to-check! [condition]
  (if (and (not (nil? *precondition-checks-performed*)) (contains? *precondition-checks-performed* condition))
    nil
    (do
      (when-not (nil? *precondition-checks-performed*)
        (conj! *precondition-checks-performed* condition))
      `(when-not ~condition
         (throw (DynaJITRuntimeCheckFailed.))))))

(defmacro ^{:private true} jit-precondition-to-check [condition]
  `(when-not ~condition
     (throw (DynaJITRuntimeCheckFailed.))))

(defn- gen-precondition-to-check [condition]
  (assert (not (map? condition)))
  (when-not (= true condition)
    (dyna-assert *jit-consider-current-value*)
    `(jit-precondition-to-check ~condition)))

#_(defn- add-precondition-to-check! [condition]
  (???))


(defn- gen-precondition-on-same-value [value]
  (case (:type value)
    :rexpr (let []
             ;; The R-expr itself should mostly be constant.
             ;; I suppose that it will want to represent that something is constant, or if would represent
             ;; that something is a constant, or something that is returned from a variable.  But then this will need to have that the expression will be something that should only get evaluated once?
             ;;
             (???))
    :rexpr-value (let []
                   ;; this is not something that we should be conditioning on in the first place.  Either this is going to be some external variable, in which the particular value is not something
                   ;; that we should condition on, or this is going to be some internal value, which is not going to change then.
                   ;; When it is something which is internal, then the value will be able to reference an internal variable, but that will again require that it is a static variable.
                   ;; I don't think that there is a way in which we will allow for this to not be a static variable given how we are generating the JIT representations.
                   (debug-repl "todo precondtion rexpr value")
                   (???))
    :value (when-not (contains? value :constant-value)
             (assert (contains? value :current-value)) ;; otherwise we can not have that this will be the same as what it is currently, so it needs to know the currentl value
             (gen-precondition-to-check
              (if (true? (:current-value value))
                (:cljcode-expr value)
                `(= ~(:current-value value) ~(:cljcode-expr value)))))

    (???)))

(defn- is-jit-expression? [x]
  (and (map? x) (#{:rexpr :rexpr-value :value :rexpr-value-list :rexpr-list} (:type x))))

(defn- concat-code [& args]
  (let [a (remove #(or (nil? %) (boolean? %) (string? %) (number? %))
                  (map #(if (is-jit-expression? %) (:cljcode-expr %) %)
                       (drop-last args)))
        l (last args)]
    (if (is-jit-expression? l)
      (assoc l :cljcode-expr `(let* [] ~@a ~(:cljcode-expr l)))
      `(let* [] ~@a ~l))))

(defn- add-precondition-on-same-value! [value]
  (add-to-generation! (gen-precondition-on-same-value value)))

(def ^:private evaluate-symbol-meta (atom {}))  ;; symbols like 'do, are compiler builtins and not variables, so we can't easily associate meta with them

(declare ^{:private true} simplify-jit-internal-rexpr)

(defn- get-current-value [value]
  (case (:type value)
    :value (cond (contains? value :constant-value) (:constant-value value)
                 (and (contains? value :current-value) *jit-consider-current-value*) (:current-value value)
                 :else nil)
    :rexpr-value (or (:constant-value value)
                     (do
                       (assert *jit-consider-current-value*)
                       (:current-value value)))
    :rexpr-value-list (map get-current-value (:current-value value))

    ;; the R-exprs should always be able to return the current value, as it will represent the state
    :rexpr (:rexpr-type value)
    :rexpr-list (map get-current-value (:current-value value))
    (let []
      (debug-repl "todo: unknown current value type")
      (???))))

(defn- has-current-value? [value]
  (or (contains? value :constant-value)
      (and *jit-consider-current-value*
           (contains? value :current-value))))

(def ^{:private true :dynamic true}  *jit-evaluate-cljform-current* ())

(defn- jit-evaluate-cljform [expr]
  (comment
    {:value-expr nil ;; some expression which is clojure code which can be evaluated to get this value
     :rexpr-type nil ;; the R-expr which is represented by this expression
     :r-value nil ;; some instance of RexprValue (such as a variable or a constant).  I suppose that this might also be a constant
     })

  (comment
    {:type (one of :rexpr, :rexpr-value, :value, :rexpr-value-list, :rexpr-list)  ;; :rexpr means it is an R-expr type, rexpr-values means it is something like constant or variable.  Value is a value like `5`
           ;; can also be {:seq-of :rexpr} or whatever the type is
     :constant-value nil  ;; the value of this expression
     :cljcode-expr  nil   ;; code which can be placed in the generated program to return this value
     })
  (binding [*jit-evaluate-cljform-current* (cons expr *jit-evaluate-cljform-current*)]
    (cond (nil? expr) {:type :value ;; R-exprs and Rexpr-values are not allowed to take on the valid nil, so this must mean that it is of the value type
                       :constant-value nil}

          (is-jit-expression? expr) expr ;; this is already something that was evaluated by the JIT, so we are just going to pass it through

          (symbol? expr) (let [local-symbol (get *locally-bound-variables* expr)]
                           (if-not (nil? local-symbol)
                             local-symbol
                             (let [var (or (ns-resolve *rewrite-ns* expr)
                                           (get @evaluate-symbol-meta expr))
                                   m (meta var)]
                               (cond (= 'rexpr expr) {:type :rexpr
                                                      :rexpr-type *jit-currently-rewriting*} ;; return the R-expr currently getting matched
                                     (= 'simplify expr) {:type :function
                                                         :invoke (fn [[_ rexpr]]
                                                                   (let [rj (jit-evaluate-cljform rexpr)]
                                                                     (assert (= :rexpr (:type rj)))
                                                                     (debug-repl "call recursive simplify")
                                                                     (???)))}

                                     (= 'simplify-construct expr) {:type :function
                                                                   :invoke (fn [[_ rexpr]]
                                                                             (let [rj (jit-evaluate-cljform rexpr)]
                                                                               (assert (= :rexpr (:type rj)))
                                                                               ;(debug-repl "call some recursive version of simplify")
                                                                               ;(println "TODO: something for simplify-construct")
                                                                               ;; simplify construct will become a NOOP in the JIT, as these rewrites
                                                                               ;; still have to get scheduled at a global level
                                                                               ;; hence, the act of calling this method is just not going to do anything
                                                                               rj))}

                                     (= 'simplify-fast expr) (???)
                                     (= 'simplify-inference expr) (???)

                                     (= '. expr) {:type :function
                                                  :invoke (fn [[_ self method & args]]
                                                            (let [s (jit-evaluate-cljform self)
                                                                  a (doall (map jit-evaluate-cljform args))
                                                                  clj `(. ~(:cljcode-expr s) ~(ensure-simple-symbol method) ~@(map :cljcode-expr a))]
                                                              {:type :value
                                                               :cljcode-expr clj}))}

                                     (nil? var)
                                     (do
                                       (debug-repl "unknown local var")
                                       (???)
                                       #_{:type :function
                                          :invoke (fn [[e & o]]
                                                    {:type :value
                                                     :cljcode-expr `(~e ~(map jit-evaluate-cljform))})})

                                     (contains? m :dyna-jit-inline)
                                     {:type :function
                                      :invoke (:dyna-jit-inline m)}

                                     ;; for functions that we want to call externally, will still exist with this value.
                                     (:dyna-jit-external m false)
                                     {:type :function
                                      :invoke (fn [[func & args]]
                                                (let [s (var-get var)
                                                      av (doall
                                                          (for [v (map jit-evaluate-cljform args)]
                                                            (case (:type v)
                                                              :value (:cljcode-expr v)
                                                              :rexpr-value (let []
                                                                             (cond (or (instance? jit-exposed-variable-rexpr (:matched-variable v))
                                                                                       (instance? jit-hidden-variable-rexpr (:matched-variable v)))
                                                                                   (:cljcode-expr v)

                                                                                   (instance? jit-local-variable-rexpr (:matched-variable v))
                                                                                   (do
                                                                                     ;; the local variable will be something that needs to get filtered out when this comes out
                                                                                     ;; to a top level expression?  But if there is some representation which will have that it
                                                                                     `(jit-local-variable-rexpr. (quote ~(-> v :matched-variable :local-var-symbol))))
                                                                                   (instance? jit-expression-variable-rexpr (:matched-variable v)) (???)))
                                                              (do
                                                                (debug-repl "can not pass type")
                                                                (???)))))
                                                      clj `(~s ~@av)]
                                                  ;(dyna-assert (every? #(= :value (:type %)) a)) ;; if this an R-expr it would have to get materalized, a variable will need special handling as well here.... something like it should get the current variable, but if it is something local, then it will need to use a representation which corresponds with the local variable.
                                                  ;(dyna-debug (every? :cljcode-expr a))

                                                  ;; in the case that this will have a local variable, we should be able to pass through some "constant" representation to the local name.  In which case that variable would hopefully not come out of the expression and stay contained inside of the expression.  However, if this will have that there is some kind of representation for this
                                                  ;; I suppose that this should be ok for now
                                                  {:type :value
                                                   :cljcode-expr clj}))}

                                     (:macro m)
                                     {:type :function
                                      :invoke (fn [form]
                                                (try (jit-evaluate-cljform (binding [*ns* *rewrite-ns*]
                                                                             (macroexpand form)))
                                                     (catch StackOverflowError err (throw (RuntimeException. (str "Stack overflow " form))))))}

                                     (contains? @evaluate-symbol-meta expr)
                                     {:type :function
                                      :invoke (:dyna-jit-inline (get @evaluate-symbol-meta expr))}


                                     (contains? m :rexpr-constructor)
                                     (if (:no-simp-rexpr-constructor m)
                                       {:type :function
                                        :invoke (fn [[sn & args]]
                                                  (let [argv (doall (map jit-evaluate-cljform args))
                                                        argg (for [g argv]
                                                               (case (:type g)
                                                                 :rexpr (:rexpr-type g)
                                                                 :value (do
                                                                          (dyna-assert (contains? g :constant-value))
                                                                          (get-current-value g))
                                                                 :rexpr-value (cond (contains? g :matched-variable) (:matched-variable g)
                                                                                    (contains? g :constant-value) (:constant-value g)
                                                                                    :else (???))
                                                                 :rexpr-list (vec (get-current-value g))
                                                                 :rexpr-value-list (do
                                                                                     (debug-repl)
                                                                                     (???))
                                                                 ))]
                                                    {:type :rexpr
                                                     :rexpr-type (apply (resolve sn) argg)}))}
                                       {:type :function
                                        :invoke (fn [[sn & args]]
                                                  (jit-evaluate-cljform `(~'simplify-construct (~(symbol "dyna.rexpr-constructors" (str "make-no-simp-" (:rexpr-constructor m)))
                                                                                                ~@args))))})

                                     (and (ifn? (var-get var)) (#{(find-ns 'clojure.core)
                                                                  (find-ns 'clojure.set)
                                                                  (find-ns 'dyna.iterators)}
                                                                (:ns m)))
                                     {:type :function
                                      :constant-value (var-get var)
                                      :cljcode-expr (symbol var)
                                      :invoke (fn [[func & args]]
                                                (let [avals (vec (map jit-evaluate-cljform args))
                                                      can-eval (every? has-current-value? avals)
                                                      ret {:type :value
                                                           :cljcode-expr `(~(var-get var) ~@(map :cljcode-expr avals))}
                                                      result (when can-eval
                                                               (apply (var-get var) (map get-current-value avals)))]
                                                  (if can-eval
                                                    (if (every? #(contains? % :constant-value) avals)
                                                      (assoc ret
                                                             :constant-value result
                                                             :cljcode-expr result)
                                                      (assoc ret
                                                             :current-value result))
                                                    ret)))}

                                     ;; (and (ifn? (var-get var)) (#{find-ns 'dyna.iterators} (:ns m)))
                                     ;; {:type :function
                                     ;;  :invoke (fn [[func & args]]

                                     ;;            )}

                                     ;; (#{iterators/make-unit-iterator} var)

                                     :else
                                     (do (debug-repl "symbol ??" false)
                                         (???))))))
          (rexpr? expr) (let []
                          {:type :rexpr
                           :rexpr-type expr})

          (instance? RexprValue expr) (cond (is-constant? expr)
                                            {:type :rexpr-value
                                             :constant-value expr
                                             :current-value expr
                                             :cljcode-expr `(make-constant ~(get-value expr))}

                                            (instance? jit-exposed-variable-rexpr expr)
                                            {:type :rexpr-value
                                             :current-value (*current-assignment-to-exposed-vars* (:exposed-name expr))
                                             :cljcode-expr `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                               ~(:exposed-name expr))
                                             :matched-variable expr}

                                            (instance? jit-local-variable-rexpr expr)
                                            (if (contains? @*local-variable-names-for-variable-values* expr)
                                              (let [x (@*local-variable-names-for-variable-values* expr)]
                                                {:type :rexpr-value
                                                 :matched-variable expr
                                                 :current-value (strict-get x :current-value)
                                                 :cljcode-expr `(make-constant ~(strict-get x :var-name))})
                                              {:type :rexpr-value
                                               :matched-variable expr})

                                            (instance? jit-expression-variable-rexpr expr)
                                            {:type :rexpr-value
                                             :cljcode-expr (:cljcode expr)
                                             :matched-variable expr}

                                            :else (do
                                                    (debug-repl "unknown rexpr value")
                                                    (???)))

          (keyword? expr) (let []
                            {:type :value
                             :constant-value expr
                             :invoke (fn [[kw & body]]
                                       (let [b (map jit-evaluate-cljform body)
                                             s (first b)]
                                         (debug-repl "keyword invoked")
                                         (???)

                                         (if (= :rexpr (:type s))
                                           (do
                                             ;; this is accessing a field on an R-expr.  It should just replace this lookup with directly accessing the value
                                             )
                                           (do
                                             (assert (= :value (:type s)))
                                             ;; this is just accessing a field on a map, which we will just emit directly
                                             )
                                           )
                                         (???)))})
          (vector? expr) (let [vs (map jit-evaluate-cljform expr)
                               types (into #{} (map :type vs))
                               constant (every? #(contains? % :constant-value) vs)]
                           (assert (= 1 (count types)))
                           (if (= (first types) :rexpr)
                             {:type :rexpr-list
                              :current-value (vec vs)}
                             (merge {:type (case (first types)
                                             :rexpr-value :rexpr-value-list
                                             :value :value)
                                     :cljcode-expr (vec (map #(:cljcode-expr % `(bad-gen "vector arg no code")) vs))}
                                    (when constant
                                      {:constant-value (vec (map :constant-value vs))}))))

          (instance? clojure.lang.APersistentMap expr)
          (let [all-constant (volatile! true)
                ;; the map can only be a map of values to values (I think the cases where it is a map or R-exprs will simply not be supported by the JIT)
                m (into {} (for [[k v] expr
                                 :let [kj (jit-evaluate-cljform k)
                                       vj (jit-evaluate-cljform v)]]
                             (do (when (or (not (contains? kj :constant-value))
                                           (not (contains? vj :constant-value)))
                                   (vreset! all-constant false))
                                 (assert (= (:type kj) :value)) ;; TODO: might want to allow other types to go here
                                 (assert (= (:type vj) :value))
                                 [(:cljcode-expr kj) (:cljcode-expr vj)])))]
            (if @all-constant
              {:cljcode-expr m :constant-value m :type :value}
              {:cljcode-expr m :type :value}))

          (or (boolean? expr) (number? expr) (string? expr) (and (seqable? expr) (empty? expr)))
          {:cljcode-expr expr :type :value :constant-value expr}

          (instance? Aggregator expr) {:type :value
                                       :constant-value expr
                                       :current-value expr
                                       :cljcode-expr (with-meta (symbol "dyna.rexpr-aggregators" (str "defined-aggregator-" (:name expr)))
                                                       {:tag "dyna.rexpr_aggregators.Aggregator"})}

          (seqable? expr) ;; vector has already been checked, so this is going to only be list-like things
          (let [f (jit-evaluate-cljform (first expr))
                r ((:invoke f (fn [[_ & args]]
                                ;; the default invoke which will just generate some code here for the function call
                                (let [s (strict-get f :cljcode-expr)
                                      a (doall (map #(strict-get (jit-evaluate-cljform %) :cljcode-expr) args))]
                                  {:type :value
                                   :cljcode-expr `(~s ~@a)})))
                   expr)]
            (dyna-assert (#{:rexpr :rexpr-value :value :function :void :rexpr-list :rexpr-value-list} (:type r)))
            r)

          (fn? expr)
          {:type :function
           :invoke (fn [[f & args]]
                     {:type :value
                      :cljcode-expr `(~f ~@(map #(strict-get (jit-evaluate-cljform %) :cljcode-expr) args))})}

          :else
          (do (debug-repl "unknown expression type")
              (???)))))



(swap! evaluate-symbol-meta assoc 'let*
       {:dyna-jit-inline (fn [form]
                           (let [[_ bindings & body] form
                                 [rbind rbody] ((fn rec [varassigns body]
                                                  (if (empty? varassigns)
                                                    (let [acts (map jit-evaluate-cljform body)]
                                                      (if (empty? acts)
                                                        [() {:type :value
                                                             :cljcode-expr nil
                                                             :constant-value nil}]
                                                        (let [l (last acts)
                                                              l2 (assoc l :cljcode-expr `(let* [] ~@(map :cljcode-expr acts)))]
                                                          [() l2])))
                                                    (let [[varname value & other] varassigns
                                                          value-expr (jit-evaluate-cljform value)
                                                          cljcode-expr (:cljcode-expr value-expr)]
                                                      (if (or (symbol? cljcode-expr) (number? cljcode-expr) (string? cljcode-expr) (boolean? cljcode-expr)) ;; if "simple" don't make a new var
                                                        (binding [*locally-bound-variables* (assoc *locally-bound-variables*
                                                                                                   varname
                                                                                                   (assoc value-expr :local-var cljcode-expr))]
                                                          (let [[inner-binding res] (rec other body)]
                                                            [inner-binding res]))
                                                        (let [local-variable-name (gensym varname)]
                                                          ;; make a new variable and assign the value to the variable, as it will be something that is "too complex" to potentially evaluate multiple times
                                                          (binding [*locally-bound-variables* (assoc *locally-bound-variables*
                                                                                                     varname (assoc value-expr :local-var local-variable-name))]
                                                            (let [[inner-binding res] (rec other body)]
                                                              [(cons local-variable-name (cons (:cljcode-expr value-expr) inner-binding)) res])))))))
                                                bindings body)]
                             (assoc rbody :cljcode-expr `(let* ~(vec rbind) ~(:cljcode-expr rbody)))))})

(swap! evaluate-symbol-meta assoc 'do
       {:dyna-jit-inline (fn [form]
                           (let [acts (into [] (map jit-evaluate-cljform (rest form)))]
                             (if (empty? acts)
                               {:type :value
                                :cljcode-expr nil
                                :constant-value nil}
                               (let [l (last acts)
                                     l2 (assoc l :cljcode-expr `(do ~@(map :cljcode-expr acts)))]
                                 l2))))})

(swap! evaluate-symbol-meta assoc 'quote
       {:dyna-jit-inline (fn [[_ q]]
                           {:cljcode-expr `(quote ~q)
                            :constant-value q
                            :type :value})})

(swap! evaluate-symbol-meta assoc 'fn*
       {:dyna-jit-inline (fn [form]
                           (debug-repl "attempting to evaluate function creation") ;; this is not going to work that well.... I suppose that this could create the function and handle renamed variables....
                           (???))})

(swap! evaluate-symbol-meta assoc 'if
       {:dyna-jit-inline (fn [[_ cond true-b false-b]]
                           (let [condv (jit-evaluate-cljform cond)
                                 cval (when (has-current-value? condv)
                                        (get-current-value condv))]
                             (if-not (has-current-value? condv)
                               (binding [*jit-generate-functions* (if (nil? *jit-generate-functions*)
                                                                    nil
                                                                    () ;; this will cause an error if anything attempts to generate inside of the if branch
                                                                    )]
                                 (let [true-r (jit-evaluate-cljform true-b)
                                       false-r (jit-evaluate-cljform false-b)]
                                   (assert (and (= :value (:type true-r)) (= :value (:type false-r))))
                                   {:type :value
                                    :cljcode-expr `(if ~(:cljcode-expr condv)
                                                     ~(:cljcode-expr true-r)
                                                     ~(:cljcode-expr false-r))}))
                               (if cval
                                 (concat-code
                                  (gen-precondition-to-check (:cljcode-expr condv))
                                  (jit-evaluate-cljform true-b))
                                 (concat-code
                                  (gen-precondition-to-check `(not ~(:cljcode-expr condv)))
                                  (jit-evaluate-cljform false-b))))))})

(swap! evaluate-symbol-meta assoc 'loop*
       {:dyna-jit-inline (fn [[_ init & body]]
                           ;; a loop inside of the JIT would have to figure out what the return types are.  Also this would have to deal with different
                           ;; values during every step of the loop.  I suppose that this should not really need to be something that we are worried about in the first place
                           (???))})

(defn- set-jit-method [v f]
  (if (var? v)
    (doseq [x (:all-vars (meta v) (list v))]
      (alter-meta! x assoc :dyna-jit-inline f))
    (doseq [x v]
      (set-jit-method x f))))

(defn- is-bound-jit? [v]
  (cond (is-constant? v) true
        (contains? @*local-variable-names-for-variable-values* v) true
        (instance? jit-local-variable-rexpr v) false ;; if this is bound, it will be contained in the local-variable-names map
        (instance? jit-expression-variable-rexpr v) true
        (instance? jit-exposed-variable-rexpr v) (let [w (jit-evaluate-cljform `(is-bound? ~v))
                                                       r (get-current-value w)]
                                                   (add-precondition-on-same-value! w)
                                                   (when r
                                                     ;; if this variable is bound, then we will also get the variable value which
                                                     ;; will catch the fact that there is some value for this variable.
                                                     ;; though we might only care that the variable is bound instead of the exact value of the variable
                                                     ;; I suppose that the is-bound-jit function is only called from internal code,
                                                     ;; so that should not be that big of an issue.....
                                                     (jit-evaluate-cljform `(get-value ~v)))
                                                   r)
        ;(instance? jit-placeholder-variable-rexpr v) (is-bound-jit? (:wrapped v))

        :else (do
                (debug-repl "unknown bound")
                (???))))


;; for expressions which can be evaluated when there is a current value, but otherwise we are not going to know
;; what the expression returns
(set-jit-method
 #'is-bound?
 (fn [[n arg]]
   (let [varj (jit-evaluate-cljform arg)]
     (assert (= :rexpr-value (:type varj)))
     (cond (is-constant? (:constant-value varj))
           {:type :value
            :constant-value true
            :cljcode-expr true}

           (contains? @*local-variable-names-for-variable-values* (:matched-variable varj))
           {:type :value
            :constant-value true
            :cljcode-expr true}

           (instance? jit-expression-variable-rexpr (:matched-variable varj))
           {:type :value
            :constant-value true
            :cljcode-expr true}

           (instance? jit-local-variable-rexpr (:matched-variable varj))
           {:type :value
            :constant-value false
            :cljcode-expr false}

           (and (not *jit-consider-current-value*) (instance? jit-exposed-variable-rexpr (:matched-variable varj)))
           {:type :value
            :cljcode-expr `(is-bound-in-context? ~(:cljcode-expr varj) ~'**context**)}

           :else
           (do
             (dyna-assert (:current-value varj))
             {:type :value
              :cljcode-expr `(is-bound-in-context? ~(:cljcode-expr varj) ~'**context**)
              :current-value (is-bound? (get-current-value varj))})))))

(set-jit-method
 #'is-constant?
 (fn [[n arg]]
   (let [varj (jit-evaluate-cljform arg)
         cval (get-current-value varj)
         const (contains? varj :constant-value)
         result (is-constant? cval)]
     (merge {:type :value
             :cljcode-expr (if const result `(is-constant? ~(:cljcode-expr varj)))}
            (when (contains? varj :constant-value)
              {:constant-value result})
            (when (contains? varj :current-value)
              {:current-value result})))))

(set-jit-method
 #'is-variable?
 (fn [[n arg]]
   (let [varj (jit-evaluate-cljform arg)]
     (cond (or (instance? jit-local-variable-rexpr (:matched-variable varj))
               (instance? jit-hidden-variable-rexpr (:matched-variable varj))) {:type :value :constant-value true :cljcode-expr true}

           (or (is-constant? (:constant-value varj)) (is-constant? (:matched-variable varj))) {:type :value :constant-value false :cljcode-expr false}

           ;; the exposed variable needs to be handled specially because it
           ;; depends on what is in the placeholder for that value.  So it could
           ;; be a constant
           (instance? jit-exposed-variable-rexpr (:matched-variable varj))
           (merge {:type :value
                   :cljcode-expr `(is-variable? ~(:cljcode-expr varj))}
                  (when *jit-consider-current-value*
                    {:current-value (is-variable? (get-current-value varj))}))


           :else
           (do
             (debug-repl "is-var")
             (???))))))

#_(set-jit-method
 [#'is-constant?
  #'is-variable?]
 (fn [[n arg]]
   (let [varj (jit-evaluate-cljform arg)
         cval (get-current-value varj)
         func (var-get (ns-resolve 'dyna.rexpr n))
         result (func cval)
         ;all-args-constant (every? #(contains? % :constant-value) varj)
         ;all-args-known (every? #(or (contains? % :constant-value) (contains? % :current-value)) varj)
         ]
     (merge {:type :value
             :cljcode-expr `(~n ~(:cljcode-expr varj))}
            (when (contains? varj :constant-value)
              {:constant-value result})
            (when (contains? varj :current-value)
              {:current-value result})))))

(set-jit-method
 #'get-value
 (fn [[_ var]]
   (let [varj (jit-evaluate-cljform var)
         ;cval (get-current-value varj)
         ;result (get-value cval)
         ]
     (dyna-assert (= :rexpr-value (:type varj)))
     (cond (is-constant? (:constant-value varj))
           {:type :value
            :constant-value (get-value (:constant-value varj))
            :cljcode-expr (get-value (:constant-value varj))}

           (contains? @*local-variable-names-for-variable-values* (:matched-variable varj))
           (let [x (@*local-variable-names-for-variable-values* (:matched-variable varj))]
             {:type :value
              :cljcode-expr (strict-get x :var-name)
              :current-value (strict-get x :current-value)})

           (instance? jit-expression-variable-rexpr (:matched-variable varj))
           {:type :value
            :cljcode-expr (:cljcode (:matched-variables varj))}

           (instance? jit-exposed-variable-rexpr (:matched-variable varj))
           (let [cval (when *jit-consider-current-value*
                        (get-current-value varj))]
             (if (nil? cval)
               ;; if there is no current value, then we will just return the code which returns the current value
               ;; but we are unable to figure out what the current value for this is
               {:type :value
                :cljcode-expr `(get-value-in-context ~(:cljcode-expr varj) ~'**context**)}
               (do
                 (assert (is-bound? cval))
                 (if (can-generate-code?)
                   (let [local-name (gensym 'local-cache)]
                     (add-to-generation! (fn [inner]
                                           `(let* [~local-name (get-value-in-context ~(:cljcode-expr varj) ~'**context**)]
                                              ~(inner))))
                     (vswap! *local-variable-names-for-variable-values* assoc (:matched-variable varj) {:var-name local-name
                                                                                                        :current-value (get-value cval)
                                                                                                        :bound-from-outer-context true})
                     {:type :value
                      :current-value (get-value cval)
                      :cljcode-expr local-name})
                   {:type :value
                    :current-value (get-value cval)
                    :cljcode-expr `(bad-gen "get value without gen cache")}))))

           (instance? jit-local-variable-rexpr (:matched-variable varj))
           (let []
             (debug-repl "bad gen calling get value unbound")
             {:type :value
              :cljcode-expr `(bad-gen "calling get value on local variable without value being bound" ~varj)})

           :else
           (let []
             (debug-repl "some get value")
             (???)
             {:type :value
              ;:current-value result
              ;:cljcode-expr `(get-value ~(:cljcode-expr varj))
              }
             )))))

(set-jit-method
 #'set-value!
 (fn [[_ var value]]
   (let [varj (jit-evaluate-cljform var)
         valj (jit-evaluate-cljform value)
         source-clj (:cljcode-expr valj)
         local-value-name (if (symbol? source-clj)
                            source-clj
                            (gensym 'local-value))]
     (assert (can-generate-code?))
     (assert (= :value (:type valj)))
     (assert (= :rexpr-value (:type varj)))
     (assert (not (nil? *jit-generate-functions*)))
     ;; this will have to track which variables are set.
     ;; it should also have that this is going to set the value in the current context.  This will mean that it will be looking for it to find
     (when (not= source-clj local-value-name)
       (add-to-generation! (fn [inner]
                             `(let* [~local-value-name ~source-clj]
                                ;; setting the variable value to the outer context will be handled at the top of the generation loop now
                                ~(inner)))))

     ;; if the value is set to the context, then it will have that this needs
     (vswap! *local-variable-names-for-variable-values* assoc (:matched-variable varj) {:var-name local-value-name
                                                                                        :current-value (get-current-value valj)})
     {:type :void ;; indicate that this function does not have some value which is evaluated, but instead is some sideeffect?
      })))

(set-jit-method
 #'make-constant
 (fn [[_ val]]
   (let [valj (jit-evaluate-cljform val)
         c (make-constant (get-current-value valj))]
     {:type :rexpr-value
      ;:matched-variable c
      (if (contains? valj :constant-value) :constant-value :current-value) c
      :cljcode-expr `(make-constant ~(:cljcode-expr valj))})))

(set-jit-method
 #'make-constant-bool
 (fn [[_ val]]
   (let [valj (jit-evaluate-cljform val)
         b (if (get-current-value valj) true false)
         c (make-constant b)
      ;   e (jit-expression-variable-rexpr. `(if ~(:cljcode-expr valj) true false))
         ]
     ;; this is going to add a check that this is the same value
     (add-to-generation! (if b
                           `(jit-precondition-to-check ~(:cljcode-expr valj))
                           `(jit-precondition-to-check (not ~(:cljcode-expr valj)))))
     {:type :rexpr-value
      :constant-value c
      :cljcode-expr `(make-constant ~b)})))

(set-jit-method
 #'make-variable
 (fn [[_ varname]]
   (debug-repl "todo jit make variable")
   (???)))

(set-jit-method
 #'count
 (fn [[_ arg]]
   (let [varj (jit-evaluate-cljform arg)]
     (if (and (#{:rexpr-value-list :rexpr-list} (:type varj))
              (contains? varj :current-value))
       (let [c (count (:current-value varj))]
         {:type :value
          :current-value c
          :constant-value c
          :cljcode-expr c})
       (do
         (debug-repl "count method")
         (???))))))

(set-jit-method
 #'map
 (fn [[_ func & args]]
   (let [funj (jit-evaluate-cljform func)
         varjs (doall (map jit-evaluate-cljform args))]
     (assert (and (not (empty? varjs))
                  (:invoke funj)
                  (every? #(and (contains? % :current-value)
                                (#{:rexpr-value-list :rexpr-list} (:type %)))
                          varjs)))
     (let [new-vals (doall (for [group-vals (apply map list (map :current-value varjs))]
                             ((:invoke funj) (cons func group-vals))))
           types (into #{} (map :type new-vals))
           cljcode (map #(:cljcode-expr % `(bad-gen "bad map")) new-vals)]
       ;(debug-repl "jit map")
       (assert (= 1 (count types)))
       {:type (case (first types)
                :rexpr :rexpr-list
                :value :value
                :rexpr-value :rexpr-value-list)
        :current-value (if (= :value (first types))
                         (map get-current-value new-vals)
                         new-vals)
        :cljcode-expr `(list ~@cljcode)}
       ))))

(set-jit-method
 #'vec
 (fn [[_ col]]
   (let [varj (jit-evaluate-cljform col)]
     (case (:type varj)
       :rexpr-list varj  ;; these will just pass through unchecked, as they are giong to end up handled by something else
       :rexpr-value-list varj
       :value (merge {:type :value
                      :cljcode-expr
                      (let [cc (:cljcode-expr varj)]
                        (cond (vector? cc) cc
                              (and (seqable? cc) (#{'list 'clojure.core/list clojure.core/list} (first cc))) `[~@(rest cc)]  ;; this would be like (vec (list 1 2 3)), so just shortcut this to be [1 2 3]
                              :else `(vec ~cc)))}
                     (when (contains? varj :current-value)
                       {:current-value (vec (:current-value varj))}))))))

(set-jit-method
 #'apply
 (fn [[_ func & args]]
   (let [funcj (jit-evaluate-cljform func)
         argsj (doall (map jit-evaluate-cljform args))]

     (if-not (empty? argsj)
       (let [p (drop-last argsj)
             cc (:cljcode-expr (last argsj))
             [lst can-lst] (cond (vector? cc) [cc true]
                                 (and (seqable? cc) (not (vector? cc)) (#{'list 'clojure.core/list} (first cc))) [(rest cc) true]
                                 :else [nil false])
             jc (if can-lst
                  `(~(strict-get funcj :cljcode-expr) ~@(map :cljcode-expr (drop-last argsj)) ~@lst)
                  `(apply ~(strict-get funcj :cljcode-expr) ~@(map :cljcode-expr argsj)))]
         ;(debug-repl "apply" false)
         {:type :value
          :cljcode-expr jc})
       (jit-evaluate-cljform (list funcj)) ;; then it is getting called with no arguments
       ))))

(set-jit-method
 #'reify
 (fn [[_ & args]]
   (throw (RuntimeException. "Reify not supported in JITtted code, make a function which can be called from the JITted code and mark it :dyna-jit-external"))))

(set-jit-method
 [#'context/make-empty-context
  #'context/make-nested-context-disjunct
  #'context/make-nested-context-proj
  #'context/make-nested-context-if-conditional
  #'context/make-nested-context-aggregator
  #'context/make-nested-context-memo-conditional
  #'context/make-nested-context-aggregator-op-outer
  #'context/make-nested-context-aggregator-op-inner
  #'context/bind-context
  #'context/bind-context-raw
  #'context/bind-no-context
  #'get-user-term
  #'push-thread-bindings

  #'get-value-in-context
  #'is-bound-in-context?
  #'get-representation-in-context
  ]
 (fn [form]
   (throw (RuntimeException. "Unsupported in JITted code"))))

(set-jit-method #'context/has-context (fn [form]
                                        {:cljcode-expr true
                                         :constant-value true
                                         :type :value}))

(set-jit-method #'debug-repl (fn [form]
                               {:cljcode-expr form
                                :type :value}))

(set-jit-method
 [#'or #'and]
 (fn [[m & args]]
   (case (count args)
     0 (case m
         and {:type :value :constant-value true :cljcode-expr true}
         or {:type :value :constant-value nil :cljcode-expr nil})
     1 (jit-evaluate-cljform (first args))
     (let [f (jit-evaluate-cljform (first args))]
       (cond (contains? f :constant-value)
             (case (ensure-simple-symbol m)
               and (if (:constant-value f) (jit-evaluate-cljform `(and ~@(rest args))) f)
               or (if (:constant-value f) f (jit-evaluate-cljform `(or ~@(rest args)))))

             (and (contains? f :current-value) *jit-consider-current-value*)
             (case (ensure-simple-symbol m)
               and (if (:current-value f)
                     (concat-code (gen-precondition-to-check (:cljcode-expr f))
                                  (jit-evaluate-cljform `(and ~@(rest args))))
                     (concat-code (gen-precondition-to-check `(not ~(:cljcode-expr f)))
                                  f))
               or (if (:current-value f)
                    (concat-code (gen-precondition-to-check (:cljcode-expr f))
                                 f)
                    (concat-code (gen-precondition-to-check `(not ~(:cljcode-expr f)))
                                 (jit-evaluate-cljform `(or ~@(rest args))))))
             :else
             (let [r (jit-evaluate-cljform `(~m ~@(rest args)))
                   cf (:cljcode-expr f)]
               (if (or (and (= cf true) (#{'and 'clojure.core/and} m))
                       (and (= cf false) (#{'or 'clojure.core/or} m)))
                 r ;; then there is nothing added by this first and expression, as it is already constant, and we are just ignoring the value anyways
                 {:type (:type r)
                  :cljcode-expr `(~m ~(:cljcode-expr f) ~(:cljcode-expr r))})))))))

(def ^:private matchers-override
  {:rexpr (fn [arg]
            (rexpr? arg))
   :rexpr-list (fn [arg]
                 (every? rexpr? arg))
   :any (fn [arg]
          (assert (is-rexpr-value? arg))
          true)
   :any-list (fn [arg]
               (assert (every? is-rexpr-value? arg))
               true)
   :unchecked (fn [arg] true) ;; does nothing during its check
   })


(def ^{:private true} cached-eval (memoize (fn [f]
                                             (binding [*ns* *rewrite-ns*]
                                               (eval f)))))

(defn- compute-match
  [rexpr1 matcher1]
  (let [matcher (if (map? matcher1) matcher1 {:rexpr matcher1})
        runtime-checks (volatile! [])
        currently-bound-variables (volatile! {})
        already-matched-rexprs (volatile! #{})]
    (letfn [(match-sub-expression [matcher arg arg-sig]
              (let [t (case arg-sig
                        :var :rexpr-value
                        :rexpr :rexpr
                        :mult :value
                        :value :rexpr-value
                        :str :value
                        :unchecked :unknown
                        :opaque-constant :value
                        :boolean :value
                        :file-name :value
                        :hidden-var :rexpr-value
                        :rexpr-list (do
                                      ;(debug-repl)
                                      (???))
                        :var-list :rexpr-value-list
                        :var-map (???)
                        (do (debug-repl)
                            (???)))
                    curval (cond (instance? jit-exposed-variable-rexpr arg)
                                 {:type t
                                  :current-value (*current-assignment-to-exposed-vars* (:exposed-name arg))
                                  ;; access the field directly from the type.  The top level R-expr will be assigned to the variable rexpr
                                  ;;
                                  :cljcode-expr `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                    ~(:exposed-name arg))
                                  :matched-variable arg}

                                 (instance? jit-local-variable-rexpr arg)
                                 (if (contains? @*local-variable-names-for-variable-values* arg)
                                   (let [x (@*local-variable-names-for-variable-values* arg)]
                                     {:type t
                                      :matched-variable arg
                                      :current-value (strict-get x :current-value)
                                      :cljcode-expr `(bad-gen "local variable 1")})
                                   {:type t
                                    :matched-variable arg})

                                 (is-constant? arg)
                                 {:type :rexpr-value
                                  :constant-value arg
                                  :current-value arg
                                  :cljcode-expr `(make-constant ~(get-value arg))}

                                 (rexpr? arg)
                                 {:type :rexpr
                                  :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                  :rexpr-type arg}

                                 (= t :value)
                                 {:type :value
                                  :current-value arg
                                  ;; the value should already be embedded in the R-expr in this case, so there is no need to retrieve the value
                                  :constant-value arg  ;; these should be constant values which are embed already
                                  :cljcode-expr arg}

                                 (= t :rexpr-value-list)
                                 {:type :rexpr-value-list
                                  :cljcode-expr `(bad-gen "rexpr value list 1") ;; we can not directly generate this representation?  Though the individual variables should still be accessable?
                                  :matched-variable arg
                                  :current-value (vec (for [z arg]
                                                        (cond (instance? jit-exposed-variable-rexpr z)
                                                              {:type :rexpr-value
                                                               :current-value (*current-assignment-to-exposed-vars* (:exposed-name z))
                                                               :cljcode-expr `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                                                 (:exposed-name z))
                                                               :matched-variable z}

                                                              (instance? jit-local-variable-rexpr z)
                                                              (if (contains? @*local-variable-names-for-variable-values* z)
                                                                (let [x (@*local-variable-names-for-variable-values* z)]
                                                                  {:type :rexpr-value
                                                                   :matched-variable z
                                                                   :current-value (strict-get x :current-value)
                                                                   :cljcode-expr `(bad-gen "local variable 2")})
                                                                {:type :rexpr-value
                                                                 :matched-variable arg})

                                                              :else (let []
                                                                      (debug-repl "TODO")
                                                                      (???)))))}

                                 :else
                                 (let []
                                   (debug-repl "TODO")
                                   (???)))
                    ]
                (cond (= '_ matcher) (list true) ;; successful match
                      (symbol? matcher) (if (contains? @currently-bound-variables matcher)
                                          (let [scv (get-current-value curval)
                                                mv (get @currently-bound-variables matcher)
                                                mcv (get-current-value mv)]
                                            (if (= scv mcv)
                                              (do (when-not (or (= (:cljcode-expr mv) (:cljcode-expr curval))
                                                                (and (contains? mv :constant-value) (contains? curval :constant-value)))
                                                    (vswap! runtime-checks conj (gen-precondition-to-check `(= (:cljcode-expr mv) (:cljcode-expr curval)))))
                                                  (list true))
                                              nil ;; does not match
                                              ))
                                          (do
                                            (when-not (= '_ matcher)
                                              (vswap! currently-bound-variables assoc matcher curval))
                                            (list true)))

                      (and (= 2 (count matcher))
                           (not (contains? @rexpr-containers-signature (car matcher)))
                           (symbol? (cdar matcher))
                           (contains? @rexpr-matchers-meta (car matcher)))
                      (let [match-requires (car matcher)
                            match-requires-meta (get @rexpr-matchers-meta match-requires)
                            match-success (if (contains? matchers-override match-requires)
                                            (let [r ((matchers-override match-requires) arg)]
                                              {:type :value
                                               :constant-value r
                                               :cljcode-expr r})
                                            (binding [*locally-bound-variables* {(first (:matcher-args match-requires-meta))
                                                                                 curval}]
                                              (jit-evaluate-cljform (:matcher-body match-requires-meta))))]
                        (if (get-current-value match-success)
                          (if (contains? @currently-bound-variables (cdar matcher))
                            (let [mv (get @currently-bound-variables (cdar matcher))
                                  mcv (get-current-value mv)
                                  scv (get-current-value curval)]
                              (if (= mcv scv)
                                (do
                                  (when-not (or (= (:cljcode-expr mv) (:cljcode-expr curval))
                                                (and (contains? mv :constant-value) (contains? curval :constant-value)))
                                    (vswap! runtime-checks conj (gen-precondition-to-check `(= (:cljcode-expr mv) (:cljcode-expr curval)))))
                                  (vswap! runtime-checks conj (gen-precondition-on-same-value match-success))
                                  ;; this is already bound, so we do not need to set the currently bound values
                                  (list true))
                                nil ;; failed to match the existing value
                                ))
                            (do
                              (when-not (contains? match-success :constant-value)
                                (vswap! runtime-checks conj (gen-precondition-to-check (:cljcode-expr match-success))))
                              (when-not (= '_ (cdar matcher))
                                (vswap! currently-bound-variables assoc (cdar matcher) curval))
                              (list true)))
                          nil ;; match of condition failed
                          ))

                      (contains? @rexpr-containers-signature (car matcher))
                      (let [rx (:rexpr-type curval)]
                        (assert (= :rexpr (:type curval)))
                        (match-rexpr matcher rx))

                      (and (symbol? (car matcher))
                           (symbol? (cdar matcher))
                           (= 2 (count matcher))
                           (ns-resolve *rewrite-ns* (car matcher)))
                      (let [f (ns-resolve *rewrite-ns* (car matcher))
                            cv (get-current-value curval)
                            success (f cv)]
                        (if success
                          (do
                            (when-not (contains? curval :constant-value)
                              (vswap! runtime-checks conj (gen-precondition-to-check `(~f ~(:cljcode-expr curval)))))
                            (when-not (= '_ (cdar matcher))
                              (vswap! currently-bound-variables assoc (cdar matcher) curval))
                            (list true))
                          nil))

                      (and (or (#{'fn 'fn*} (caar matcher))  ;; an inline function is used for the matcher
                               (seqable? (car matcher)))
                           (symbol? (cdar matcher))
                           (= 2 (count matcher)))
                      (let [f (cached-eval (car matcher))
                            cv (get-current-value curval)
                            success (f cv)]
                        (if success
                          (do
                            (when-not (contains? curval :constant-value)
                              (vswap! runtime-checks conj (gen-precondition-to-check `(~f (:cljcode-expr curval)))))
                            (when-not (= '_ (cdar matcher))
                              (vswap! currently-bound-variables assoc (cdar matcher) curval))
                            (list true))
                          nil ;; match fail
                          ))

                      :else
                      (do (debug-repl "unknown match condition")
                          (???)))
                ))
            (match-rexpr [matcher rexpr]
              (assert (rexpr? rexpr))
              (let [rname (rexpr-name rexpr)
                    args (get-arguments rexpr)
                    rsignature (get @rexpr-containers-signature rname)]
                (if (= rname (first matcher))
                  ((fn rec [match-expr-seq arg-seq rsignature-seq]
                     (if (and (empty? match-expr-seq) (empty? arg-seq) (empty? rsignature-seq))
                       (list true)
                       (let [match-expr (first match-expr-seq)
                             arg (first arg-seq)
                             [arg-sig _] (first rsignature-seq)]
                         (for [_ (match-sub-expression match-expr arg arg-sig)
                               _ (rec (rest match-expr-seq) (rest arg-seq) (rest rsignature-seq))]
                           true))))
                   (rest matcher) args rsignature)
                  () ;; no match
                  )))
            (match-context [matcher]
              (if (vector? matcher) ;; if we have to match multiple things at the same time from the context
                ((fn r [s]
                   (if (empty? s)
                     (list true)
                     (for [_ (match-context (first s))
                           _ (r (rest s))]
                       true)))
                 matcher)
                (let [cur-checks @runtime-checks
                      cur-bound @currently-bound-variables
                      cur-already-matched @already-matched-rexprs]
                  (assert (not *rewrites-allowed-to-use-inference-context*)) ;; TODO: this is going to have to check the current inference context
                  (for [cr *local-conjunctive-rexprs-for-infernece*
                        :let [[proj-out rx] cr
                              __ (do
                                   (vreset! runtime-checks cur-checks)
                                   (vreset! currently-bound-variables cur-bound)
                                   (vreset! already-matched-rexprs cur-already-matched))]
                        :when (and (empty? proj-out) (not (contains? @already-matched-rexprs rx)))
                        _ (match-rexpr matcher rx)
                        :let [__ (vswap! already-matched-rexprs conj rx)]]
                    true))))
            (match-check [matcher]
              (let [success (binding [*locally-bound-variables* @currently-bound-variables]
                              (jit-evaluate-cljform matcher))]
                (when (get-current-value success)
                  (when-not (:constant-value success)
                    (vswap! runtime-checks conj (gen-precondition-to-check (:cljcode-expr success))))
                  (list true))))
            (match-top [matcher rexpr]
              (assert (every? #{:rexpr :context :check} (keys matcher))) ;; this is checked in rexpr.clj, but check again here as it could otherwise become forgotten
              (for [_ (match-rexpr (:rexpr matcher) rexpr)
                    :let [__ (vreset! already-matched-rexprs #{rexpr})]
                    _ (if (contains? matcher :context)
                        (match-context (:context matcher))
                        (list true))
                    _ (if (contains? matcher :check)
                        (match-check (:check matcher))
                        (list true))]
                true))]
      (doall (for [_ (match-top matcher rexpr1)]
               [@runtime-checks @currently-bound-variables])))))


(defn- simplify-perform-generic-rewrite [rexpr rewrite]
  (let [kw-args (:kw-args rewrite)]
    (cond (contains? kw-args :check)
          (binding [*locally-bound-variables* (merge {'rexpr {:type :rexpr
                                                              :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                                              :rexpr-type rexpr}}
                                                     (:matching-vars rewrite))
                    *rewrite-ns* (:namespace rewrite)]
            (doseq [c (:runtime-checks rewrite)
                    :when (not (nil? c))]
              (add-to-generation! c))
            (let [expression (jit-evaluate-cljform (:check kw-args))]
              (if (get-current-value expression)
                (do (add-to-generation! `(when-not ~(:cljcode-expr expression)
                                           (throw (UnificationFailure. "JIT check rewrite"))))
                    (conj! *rexpr-checked-already* rexpr)
                    (make-multiplicity 1))
                (do (add-to-generation! `(when ~(:cljcode-expr expression)
                                           (throw (DynaJITRuntimeCheckFailed.))))
                    (make-multiplicity 0)))))

          (contains? kw-args :assigns-variable)
          (binding [*locally-bound-variables* (merge {'rexpr {:type :rexpr
                                                              :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                                              :rexpr-type rexpr}}
                                                     (:matching-vars rewrite))
                    *rewrite-ns* (:namespace rewrite)]
            (doseq [c (:runtime-checks rewrite)
                    :when (not (nil? c))]
              (add-to-generation! c))
            (let [assigning-var (:assigns-variable kw-args)
                  value-expression (:rewrite-body rewrite)
                  expression `(set-value! ~assigning-var ~value-expression)]
              (add-to-generation! (jit-evaluate-cljform expression))
              (conj! *rexpr-checked-already* rexpr)
              (make-multiplicity 1) ;; the result of assigning a variable will just be a mult1 expression
              ))

          (contains? kw-args :infers)
          (binding [*locally-bound-variables* (merge {'rexpr {:type :rexpr
                                                              :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                                              :rexpr-type rexpr}}
                                                     (:matching-vars rewrite))
                    *rewrite-ns* (:namespace rewrite)]
            (doseq [c (:runtime-checks rewrite)
                    :when (not (nil? c))]
              (add-to-generation! c))
            (let [inf-result (jit-evaluate-cljform (:infers kw-args))
                  ri (:rexpr-type inf-result)]
              (assert (= :rexpr (:type inf-result)))
              (let [already-contained (for [[proj-out rx] *local-conjunctive-rexprs-for-infernece*
                                            :when (= rx ri)]
                                        rx)]
                (if (and (empty? already-contained) (not (contains? *rexpr-checked-already* ri)))
                  (make-conjunct [rexpr ri]) ;; create a new conjunct to add this to the expression
                  rexpr ;; not going to add as it is already in the context
                  ))))

          (contains? kw-args :assigns)
          (???)

          :else
          (binding [*locally-bound-variables* (merge {'rexpr {:type :rexpr
                                                              :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                                              :rexpr-type rexpr}}
                                                     (:matching-vars rewrite))
                    *rewrite-ns* (:namespace rewrite)]
            (doseq [c (:runtime-checks rewrite)
                    :when (not (nil? c))]
              (add-to-generation! c))
            (let [b (:rewrite rewrite)
                  r (jit-evaluate-cljform b)]
              (assert (= :rexpr (:type r)))
             ; (add-to-generation! (:cljcode-expr r)) ;; if there are conditions on the R-exprs, that could be partially encoded here
              ;(debug-repl "perform generic rewrite")
              (:rexpr-type r))))
    #_(if (contains? :assigns-variable kw-args)
        (do
          ;; this is an assignment rewrite
          )
        (do
          (debug-repl "TODO: handle non-assigns rewrite")
          (???)))
    ))


(defn- simplify-jit-internal-rexpr-generic-rewrites [rexpr]
  (vswap! *jit-simplify-call-counter* inc)
  (let [rewrites (get @rexpr-rewrites-source (type rexpr) [])
        matching-rewrites (into [] (remove nil? (map (fn [rr]
                                                       (let [run-at (:run-at (:kw-args rr) [:standard])]
                                                         (binding [*jit-computing-match-of-rewrite* rr
                                                                   *rewrite-ns* (:namespace rr)]
                                                           (let [results (compute-match rexpr (:matcher rr))]
                                                             (when-not (empty? results)
                                                               (when (not= (count results) 1)
                                                                 (debug-repl "handle multiple success match")
                                                                 (???))
                                                               (let [[[runtime-checks currently-bound-variables]] results]
                                                                 (assoc rr
                                                                        :runtime-checks runtime-checks
                                                                        :matching-vars currently-bound-variables
                                                                        :simplify-call-counter @*jit-simplify-call-counter*)))))))
                                                     rewrites)))]
    (doseq [mr matching-rewrites]
      (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*) mr]))
    #_(when (is-unify? rexpr)
      (debug-repl "generic unify"))
    (let [picked (filter *jit-simplify-rewrites-picked-to-run* matching-rewrites)]
      (if (empty? picked)
        nil
        (if *jit-compute-unification-failure*
          (make-multiplicity 0)
          (simplify-perform-generic-rewrite rexpr (first picked)))
        #_(do
            ;; going to perform the rewrite, which means that

            (debug-repl "need to perform rewrite")
            (???))))))

#_(defn- simplify-jit-internal-rexpr [rexpr-in]
  (vswap! *jit-simplify-call-counter* inc)
  (let [rexpr (if (rexpr? rexpr-in)
                rexpr-in
                (do (assert (= :rexpr (:type rexpr-in)))
                    (:rexpr-type rexpr-in)))]
    (binding [*jit-currently-rewriting* rexpr]
      (tbinding
       [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)]
       (debug-tbinding
        [current-simplify-running simplify-jit-internal-rexpr]
        (let [jit-specific-rewrites (get @rexpr-rewrites-during-jit-compilation (type rexpr) nil)
              ret (if (nil? jit-specific-rewrites)
                    (simplify-jit-internal-rexpr-generic-rewrites rexpr)
                    (first (remove #(or (nil? %) (= % rexpr))
                                   (for [f jit-specific-rewrites]
                                     (f rexpr simplify-jit-internal-rexpr)))))]
          (if (or (nil? ret) (= ret rexpr))
            rexpr
            (let [m (get @*jit-rexpr-rewrite-metadata* rexpr)
                  c (get @*jit-rexpr-rewrite-metadata* ret)]
              ;; track the metadata as the R-expr is changed
              (cond (and (not (nil? m)) (nil? c)) (vswap! *jit-rexpr-rewrite-metadata* assoc ret m) ;; keep the same structure but assoc with the new-rexpr
                    (and (not (nil? m)) (not (nil? c))) (vreset! c (merge @c @m)) ;; merge the old metadata into the new object
                    )
              ret))))))))

(defn- simplify-jit-internal-rexpr [rexpr-in]
  (vswap! *jit-simplify-call-counter* inc)
  (let [rexpr (if (rexpr? rexpr-in)
                rexpr-in
                (do (assert (= :rexpr (:type rexpr-in)))
                    (:rexpr-type rexpr-in)))]
    (binding [*jit-currently-rewriting* rexpr]
      (tbinding
       [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)]
       (debug-tbinding
        [current-simplify-running simplify-jit-internal-rexpr]
        (let [^SimplifyRewriteCollection jit-rewrite-collection (rexpr-jit-compilation-step-collection rexpr)
              ret (if (nil? (.getRewriteListHead jit-rewrite-collection))
                    (simplify-jit-internal-rexpr-generic-rewrites rexpr)
                    (jit-rewrite-collection rexpr simplify-jit-internal-rexpr))]
          (if (or (nil? ret) (= ret rexpr))
            rexpr
            (let [m (get @*jit-rexpr-rewrite-metadata* rexpr)
                  c (get @*jit-rexpr-rewrite-metadata* ret)]
              ;; track the metadata as the R-expr is changed
              (cond (and (not (nil? m)) (nil? c)) (vswap! *jit-rexpr-rewrite-metadata* assoc ret m) ;; keep the same structure but assoc with the new-rexpr
                    (and (not (nil? m)) (not (nil? c))) (vreset! c (merge @c @m)) ;; merge the old metadata into the new object
                    )
              ret))))))))



(defn- simplify-jit-internal-rexpr-once [r & {:keys [simplify-count] :or {simplify-count 0}}]
  (let [top-conjuncts (all-conjunctive-rexprs r)
        possible-rewrites (binding [*jit-simplify-call-counter* (volatile! 0)
                                    *jit-simplify-rewrites-found* (volatile! #{})
                                    *jit-simplify-rewrites-picked-to-run* (constantly false)
                                    *jit-generate-functions* nil ;; make sure that we do not generate any code from selecting between rewrites
                                    *local-conjunctive-rexprs-for-infernece* top-conjuncts
                                    *local-variable-names-for-variable-values* (volatile! @*local-variable-names-for-variable-values*)]
                            (let [nr (simplify-jit-internal-rexpr r)]
                              (dyna-assert (= r nr)) ;; we did not pick anything to run, so the result should be the same
                              @*jit-simplify-rewrites-found*))]
    (if (empty? possible-rewrites)
      (do
                                        ;(debug-repl "no possible rewrites" false)
        r) ;; then we are "done" and we just return this R-expr unrewritten
      (loop [picked-rr-order (sort-by (fn [[simplify-stack rr]]
                                        (+ (* 1000 (count simplify-stack)) ;; prefer things at the top of the stack
                                           (if (:aggregator-assign-value false) -20000 0)
                                           (if (contains? (:kw-args rr) :check) -200000 0) ;; checks should go earlier
                                           (if (contains? (:kw-args rr) :assigns-variable) -100000 0) ;; then assignments of variables
                                           (if (:jit-hole-embed rr false) -10000 0) ;; if we can make the JIT state larger by embedding something inside
                                           (if (:aggregator-iterators (:kw-args rr) false) 10000 0) ;; avoid running the iterators if there is something else we can do as this will expand the expression at lot
                                           (case (:run-at (:kw-args rr))
                                             :construction -5000 ;; if this only runs at construction, it should go quickly first
                                             :inference 5000 ;; if this is more expensive inference, therefore run it later
                                             0) ;; otherwise just run it normal
                                           (* 10 (count (:runtime-checks rr))) ;; fewer preconditions should make it a bit more general
                                           (:simplify-call-counter rr)))
                                      possible-rewrites)]
        (when (> (count picked-rr-order) 1)
                                        ;(debug-repl "multiple possible rewrites")
          (println "multiple possible"))
        (if (empty? picked-rr-order)
          (do
            (when-not (empty? possible-rewrites)
              (debug-repl "rewrites did nothing" false))
            r)
          (let [picked-cc (second (first picked-rr-order))
                nr (binding [*jit-simplify-rewrites-picked-to-run* (fn [rr-md]
                                                                     (and (= (:simplify-call-counter rr-md) (:simplify-call-counter picked-cc))
                                                                          (= (:matching-vars rr-md) (:matching-vars picked-cc))
                                                                          (= (:kw-args rr-md) (:kw-args picked-cc))))
                             *local-conjunctive-rexprs-for-infernece* top-conjuncts]
                     (let [nr-unification-failure (binding [*jit-compute-unification-failure* true
                                                            *jit-simplify-call-counter* (volatile! 0)
                                                            *jit-simplify-rewrites-found* (volatile! #{})]
                                                    (simplify-jit-internal-rexpr r))]
                       (add-unification-failure-checkpoint! nr-unification-failure)
                       (let [pre-local-variable-name-values @*local-variable-names-for-variable-values*
                             nr (binding [*jit-simplify-call-counter* (volatile! 0)
                                          *jit-simplify-rewrites-found* (volatile! #{})]
                                  (simplify-jit-internal-rexpr r))
                             post-local-variable-name-values @*local-variable-names-for-variable-values*
                             set-extern-values (doall
                                                (for [[var val] post-local-variable-name-values
                                                      :when (and (instance? jit-exposed-variable-rexpr var)
                                                                 (not= (get pre-local-variable-name-values var) val)
                                                                 (not (:bound-from-outer-context val false)))
                                                      :let [varj (jit-evaluate-cljform var)]]
                                                  `(set-value-in-context! ~(:cljcode-expr varj) ~'**context** ~(strict-get val :var-name))))]
                         (when-not (empty? set-extern-values)
                           (add-to-generation! (fn [inner]
                                                 `(do
                                                    ~@set-extern-values
                                                    ~(inner)))))
                         (add-return-rexpr-checkpoint! nr)
                                        ;(debug-repl "result of doing rewrite" false)
                         nr
                         )))]
            (if (not= nr r)
              nr
              (recur (rest picked-rr-order)))))))))

(defn- simplify-jit-internal-rexpr-loop [rexpr]
  (loop [r (if (rexpr? rexpr)
             rexpr
             (do (dyna-assert (= :rexpr (:type rexpr)))
                 (:rexpr-type rexpr)))
         count 0]
    (if (is-jit-placeholder? r)
      r ;; if this is a placeholder, then just stop as it will be returned directly (unwrapping the JIT state)
      (let [nr (simplify-jit-internal-rexpr-once r :simplify-count count)]
        (if (not= r nr)
          (recur nr (+ count 1))
          nr)))))

()

(defn- maybe-create-rewrite [context rexpr jinfo simplify-method & {:keys [simplify-inference] :or {simplify-inference false}}]
  ;; this first needs to check if it has already attempted to create a rewrite
  ;; for this scenario, in which case it might not do anything here
  (assert (not simplify-inference))  ;; TODO:
  (let [argument-value-mappings (loop [m {}
                                       l (zipseq (get-arguments rexpr) (range))]
                                  (if (empty? l)
                                    m
                                    (let [[[f fi] & r] l]
                                      (recur (update-in m [f :index] conj fi)
                                             r))))
        local-name-to-context (zipmap (:variable-order jinfo) (get-arguments rexpr))
        generated-function
        (binding [*jit-generating-rewrite-for-rexpr* rexpr
                  *jit-generating-in-context* context
                  *rewrites-allowed-to-run* #{:standard}
                  *jit-consider-expanding-placeholders* false ;; TODO: this should eventually be true
                                        ;*jit-call-simplify-on-placeholders* false
                  *current-assignment-to-exposed-vars* local-name-to-context
                                        ;*current-simplify-stack* ()
                  *local-variable-names-for-variable-values* (volatile! nil)
                  *jit-generate-functions* (transient [])
                  *jit-incremented-status-counter* (volatile! false)
                  *rexpr-checked-already* (transient #{})
                  *jit-rexpr-rewrite-metadata* (volatile! {})]
          (tbinding
           [current-simplify-stack ()
            use-optimized-disjunct false
            memoization-make-guesses-handler (constantly false) ;; disable all guessing while we are doing compilation with the JIT
            is-generating-jit-rewrite true
            aggregator-op-contribute-value (fn [& args] (???)) ;; this should not get called directly from the JIT
            ]
           (debug-tbinding
            ;; restart these values, as we are running a nested version of simplify for ourselves
            [current-simplify-running nil]
            (let [prim-r (:prim-rexpr-placeholders jinfo)
                  ffff (when (nil? prim-r)
                         (debug-repl "nil prim r")
                         (???))
                  result (simplify-jit-internal-rexpr-loop prim-r)]
              (when (is-jit-placeholder? result)
                (let [v (if (:external-name result)
                          `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                              ~(:external-name result))
                          (:local-name result))]
                  (add-to-generation! (fn [inner]
                                        ;; then we are not going to call the inner function, and instead will just return the result of the placeholder
                                        ;; this means looking up the placeholder's name and returning that
                                        v))))
              (if (or (not= result prim-r) (is-jit-placeholder? result))
                ;; then there is something that we can generate, and we are going to want to run that generation and then evaluate it against the current R-expr
                (let [gen-fn (generate-cljcode-fn result)
                      __ (println gen-fn)
                      ;__ (debug-repl "pr0" false)
                      fn-evaled (binding [*ns* dummy-namespace]
                                  (eval `(do
                                           (ns dyna.rexpr-jit-v2)
                                           (def-rewrite-direct ~(:generated-name jinfo) [:standard] ~gen-fn))))]
                  ;(debug-repl "pr1" false)
                  fn-evaled)
                simplify-identity ;; if nothing was generated, then we are just going to return an identity function which does not do any rewriting
                )))))
        ;; evaluate the function here so that we clear all of the bindings which are specific to the JIT.   This should get back to whatever is the JIT's
        rr (generated-function rexpr simplify-method)]
    ;(assert (or (not= rr rexpr) (identical? simplify-identity generated-function)))
    #_(when (is-empty-rexpr? rr)
      (debug-repl "empty r" false))
    rr))

#_(defn- maybe-create-rewrites-inference [context rexpr jinfo]
  (???))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn- generate-nogencheck-match-cljcode [rexpr matcher1]
  (let [matcher (if (map? matcher1) matcher1 {:rexpr matcher1})
        runtime-checks (volatile! [])
        currently-bound-variables (volatile! {})
        already-matched-rexprs (volatile! #{})]
    (letfn [(match-sub-expression [matcher arg arg-sig]
              ;; this differs from the other matcher, in that we do not have the current value active.  Which means that it will
              (let [t (case arg-sig
                        :var :rexpr-value
                        :rexpr :rexpr
                        :mult :value
                        :value :rexpr-value
                        :str :value
                        :unchecked :unknown
                        :opaque-constant :value
                        :boolean :value
                        :file-name :value
                        :hidden-var :rexpr-value
                        :rexpr-list :rexpr-value-list
                        :var-list :rexpr-value-list
                        :var-map (???)
                        (do (debug-repl)
                            (???)))
                    curval (cond (instance? jit-exposed-variable-rexpr arg)
                                 {:type t
                                  :cljcode-expr `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                                                    ~(:exposed-name arg))
                                  :matched-variable arg}

                                 (instance? jit-local-variable-rexpr arg)
                                 (if (contains? @*local-variable-names-for-variable-values* arg)
                                   (let [x (@*local-variable-names-for-variable-values* arg)]
                                     {:type t
                                      :matched-variable arg
                                      ;:current-value (strict-get x :current-value)
                                      :cljcode-expr `(bad-gen "local variable 3")})
                                   {:type t
                                    :matched-variable arg})

                                 (is-constant? arg)
                                 {:type :rexpr-value
                                  :constant-value arg
                                  :current-value arg
                                  :cljcode-expr `(make-constant ~(get-value arg))}

                                 (rexpr? arg)
                                 {:type :rexpr
                                  :cljcode-expr `(bad-gen "should not generate the R-expr into the JIT code")
                                  :rexpr-type arg}

                                 (= t :value)
                                 {:type :value
                                  :current-value arg
                                  ;; the value should already be embedded in the R-expr in this case, so there is no need to retrieve the value
                                  :constant-value arg  ;; these should be constant values which are embed already
                                  :cljcode-expr arg}

                                 (= t :rexpr-value-list)
                                 {:type :rexpr-value-list
                                  :cljcode-expr (vec (map #(-> % jit-evaluate-cljform :cljcode-expr) arg))
                                        ;`(bad-gen "rexpr value list 2") ;; we can not directly generate this representation?  Though the individual variables should still be accessable?
                                        ;:matched-variable arg
                                  :current-value arg }

                                 (instance? Aggregator arg)
                                 {:type :value
                                  :cljcode-expr (symbol "dyna.rexpr-aggregators" (str "defined-aggregator-" (:name arg)))
                                  :constant-value arg}

                                 :else
                                 (let []
                                   (debug-repl "TODO")
                                   (???)))]
                (cond (= '_ matcher) (list true) ;; there is nothing here which is getting matched
                      (symbol? matcher) (if (contains? @currently-bound-variables matcher)
                                          (let [pv (@currently-bound-variables matcher)]
                                            (if (= pv curval)
                                              (list true) ;; this is already bound, so there is no need for this
                                              (do
                                                ;; in the case that this is variable, this should check that the value is the same, not that the variable
                                                ;; is the same.  But this is going to be used at all currently.....
                                                (vswap! runtime-checks conj `(= ~(:cljcode-expr curval) ~(:cljcode-expr pv)))
                                                (list true))))
                                          (do
                                            (when-not (= '_ matcher)
                                              (vswap! currently-bound-variables assoc matcher curval))
                                            (list true)))
                      (and (= 2 (count matcher))
                           (not (contains? @rexpr-containers-signature (car matcher)))
                           (symbol? (cdar matcher))
                           (contains? @rexpr-matchers-meta (car matcher)))
                      (let [match-requires (car matcher)
                            match-requires-meta (get @rexpr-matchers-meta match-requires)
                            match-simple-success (when (contains? matchers-override match-requires)
                                                   ((matchers-override match-requires) arg))]
                        (if (= true match-simple-success)
                          (let [pv (@currently-bound-variables (cdar matcher))]
                            ;; this has been successful using the simple match, and does not require any runtime checks
                            (when-not (= '_ (cdar matcher))
                              (if (nil? pv)
                                (vswap! currently-bound-variables assoc (cdar matcher) curval)
                                (vswap! runtime-checks conj `(= ~(:cljcode-expr curval) ~(:cljcode-expr pv)))))
                            (list true))
                          (let [match-success (binding [*locally-bound-variables* {(first (:matcher-args match-requires-meta))
                                                                                   curval}]
                                                (jit-evaluate-cljform (:matcher-body match-requires-meta)))
                                pv (@currently-bound-variables (cdar matcher))]
                            (vswap! runtime-checks conj (:cljcode-expr match-success))
                            (when-not (= '_ (cdar matcher))
                              (if (nil? pv)
                                (vswap! currently-bound-variables assoc (cdar matcher) curval)
                                (vswap! runtime-checks conj `(= ~(:cljcode-expr curval) ~(:cljcode-expr pv)))))
                            (when (or (not (contains? match-success :constant-value))
                                      (get-current-value match-success))
                              (list true)))))

                      (contains? @rexpr-containers-signature (car matcher))
                      (let [rx (:rexpr-type curval)]
                        (assert (= :rexpr (:type curval)))
                        (match-rexpr matcher rx))

                      (and (symbol? (car matcher))
                           (symbol? (cdar matcher))
                           (= 2 (count matcher))
                           (ns-resolve *rewrite-ns* (car matcher)))
                      (let [f (ns-resolve *rewrite-ns* (car matcher))
                            cv (when (has-current-value? curval)
                                 (get-current-value curval))
                            success (when-not (nil? cv)
                                      (f cv))]
                        (if success
                          (do
                            (when-not (contains? curval :constant-value)
                              (vswap! runtime-checks conj `(~f ~(:cljcode-expr curval))))
                            (when-not (= '_ (cdar matcher))
                              (vswap! currently-bound-variables assoc (cdar matcher) curval))
                            (list true))
                          (do
                            ;; then we are going to generate a runtime check which calls this function, as we are unable to evaluate this expression statically
                            (vswap! runtime-checks conj `(~f ~(:cljcode-expr curval)))
                            (when-not (= '_ (cdar matcher))
                              (assert (not (contains? @currently-bound-variables (cdar matcher))))
                              (vswap! currently-bound-variables assoc (cdar matcher) curval))
                            ;; return that this was a success as we are going to still do some generation for this
                            ;(debug-repl "matcher2")
                            (list true)))))))

            (match-rexpr [matcher rexpr]
              (assert (rexpr? rexpr))
              (let [rname (rexpr-name rexpr)
                    args (get-arguments rexpr)
                    rsignature (get @rexpr-containers-signature rname)]
                (if (= rname (first matcher))
                  ((fn rec [match-expr-seq arg-seq rsignature-seq]
                     (if (and (empty? match-expr-seq) (empty? arg-seq) (empty? rsignature-seq))
                       (list true) ;; the match was successful
                       (let [match-expr (first match-expr-seq)
                             arg (first arg-seq)
                             [arg-sig _] (first rsignature-seq)]
                         (for [_ (match-sub-expression match-expr arg arg-sig)
                               _ (rec (rest match-expr-seq) (rest arg-seq) (rest rsignature-seq))]
                           true))))
                   (rest matcher) args rsignature)
                  ();; no match
                  )))
            (match-top [matcher rexpr]
              (assert (every? #{:rexpr} (keys matcher))) ;; this code only supports matching the R-exprs directly for the moment
              (for [_ (match-rexpr (:rexpr matcher) rexpr)
                    :let [__ (vreset! already-matched-rexprs #{rexpr})]]
                true))]
      (doall (for [_ (match-top matcher rexpr)]
               [@runtime-checks @currently-bound-variables])))))

(defn- find-iterators-cljcode [rexpr]
  ;; return the find iterator code, if there are no iterators, then this will just retun nil.
  (if (is-jit-placeholder? rexpr)
    (let []
      ;; it needs to construct a nested context, and then call the standard "find iterators" on the nested jit-placeh
      (println "TODO need to construct context")
      ;(debug-repl "TODO need to construct context")
      `(find-iterators ~(if (:external-name rexpr)
                          `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)})
                              ~(:external-name rexpr))
                          (:local-name rexpr))))
    (let [iters-source (get @rexpr-iterators-source (type rexpr))]
      (when-not (empty? iters-source)
        (let [iter-matches (binding [*locally-bound-variables* {'rexpr {:type :rexpr
                                                                        :cljcode-expr `(bad-gen "should not generate R-expr")
                                                                        :rexpr-type rexpr}}
                                     *jit-consider-current-value* false]
                             (doall (for [[kw-args body def-ns] iters-source
                                          [runtime-checks bound-vars] (binding [*rewrite-ns* def-ns]
                                                                        (generate-nogencheck-match-cljcode rexpr (:match kw-args)))]
                                      (assoc kw-args
                                             :iter-body body
                                             :runtime-checks runtime-checks
                                             :bound-vars bound-vars
                                             :namespace def-ns))))]
          ;; then we are going to generate some union between all of the different iterator methods, which means that this should figure out which of the methods will have that this
          (when-not (empty? iter-matches)
            (let [i-clj (remove nil? (for [i iter-matches]
                                       (binding [*locally-bound-variables* (merge {'rexpr {:type :rexpr
                                                                                           :cljcode-expr `(bad-gen "should not generate R-expr")
                                                                                           :rexpr-type rexpr}}
                                                                                  (:bound-vars i))
                                                 *rewrite-ns* (:namespace i)
                                                 *jit-consider-current-value* false]
                                         ;; the when check is going to come after whatever happens from the jit-evaluate-cljform code does
                                         ;; if the
                                         (let [c (:cljcode-expr (jit-evaluate-cljform (:iter-body i)))
                                               checks (remove (partial = true) (:runtime-checks i))]
                                           (when-not (some (partial = false) checks)
                                             (if-not (empty? checks)
                                               `(when (and ~@checks)
                                                  ~c)
                                               c))))))
                  r (if (> (count i-clj) 1)
                      `(union #{} ~@i-clj)
                      (first i-clj))]
              ;; (println r)
              ;; (debug-repl "has some way to construct an iterator" false)
              r)))))))

(set-jit-method
 #'find-iterators
 (fn [[_ r]]
   (let [rv (jit-evaluate-cljform r)]
     (assert (= :rexpr (:type rv)))
     (let [v (find-iterators-cljcode (:rexpr-type rv))]
       (merge {:type :value
               :cljcode-expr v}
              (when (nil? v)
                {:constant-value nil}))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ^{:dynamic true :private true} *has-jit-rexpr-in-expression* (volatile! false))

(defn simplify-jit-create-rewrites-fast [rexpr]
  ;; create rewrites which correspond with simplify-fast
  ;; these rewrites can only look at the bindings to variable values
  ;; just like normal simplify, we are going to have that
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)
    current-simplify-running simplify-jit-create-rewrites-fast]
   (let [;ret ((get @rexpr-rewrites-func (type rexpr) simplify-identity) rexpr simplify-jit-create-rewrites-fast)
         ret ((rexpr-simplify-fast-collection rexpr) rexpr simplify-jit-create-rewrites-fast)
         ]
     (if (or (nil? ret) (= ret rexpr))
       (let [jinfo (rexpr-jit-info rexpr)]
         (if (and (not (nil? jinfo))
                  (contains? jinfo :generated-name) ;; if there is no generated name, then this is not a jitted R-expr
                  )
           (do
             (vreset! *has-jit-rexpr-in-expression* true) ;; record that we found something that could be generated, even if we don't end up doing the generation
             (maybe-create-rewrite (context/get-context) rexpr jinfo simplify-jit-create-rewrites-fast))
           ;; then nothing has changed, so we are going to check if this is a JIT type and then attempt to generate a new rewrite for it
           rexpr))
       (do
         (dyna-assert (rexpr? ret))
         ret)))))

(defn simplify-jit-create-rewrites-inference [rexpr]
  ;; create rewrites which can run during the interface state.  If there is nothing
  (println "jit inference simplification")
  rexpr
  #_(debug-binding
   [*current-simplify-stack* (conj *current-simplify-stack* rexpr)
    *current-simplify-running* simplify-jit-create-rewrites-inference]
   (let [ret ((get @rexpr-rewrites-inference-func (type rexpr) simplify-identity) rexpr simplify-jit-create-rewrites-inference)]
     (if (or (nil? ret) (= ret rexpr))
       (let [jinfo (rexpr-jit-info rexpr)]
         (if-not (nil? jinfo)
           (do
             (???)
             (maybe-create-rewrite (context/get-context rexpr jinfo simplify-jit-create-rewrites-inference :simplify-inference true)))
           rexpr))
       (do (dyna-assert (rexpr? ret))
           ret)))))

(intern 'dyna.rexpr 'simplify-jit-create-rewrites
        (fn [rexpr]
            ;; this is called from the main rewrite function which will create new rewrites inside of the R-expr
          (if-not (tlocal system/*generate-new-jit-rewrites*)
            rexpr
            (do
              (assert (context/has-context))
              (binding [*has-jit-rexpr-in-expression* (volatile! false)]
                (let [fr (simplify-jit-create-rewrites-fast rexpr)]
                  (if (and (= fr rexpr) @*has-jit-rexpr-in-expression*)
                    (simplify-jit-create-rewrites-inference rexpr)
                    fr)))))))

(defn simplify-jit-attempt-create-rewrite-for-jittype [rexpr]
  (if-not (tlocal system/*generate-new-jit-rewrites*)
    rexpr
    (let [jinfo (rexpr-jit-info rexpr)]
      (if-not (nil? jinfo)
        (let [r (tbinding [current-simplify-running simplify-jit-create-rewrites-fast
                           generate-new-jit-rewrites false]
                          (maybe-create-rewrite (context/get-context) rexpr jinfo simplify-jit-create-rewrites-fast))]
          ;(debug-repl "attempt create rewrite for jit type")
          r)
        rexpr))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (proj V R)
  :run-at :jit-compiler
  (let [conjuncts (all-conjunctive-rexprs R)
        conjuncts-existsing *local-conjunctive-rexprs-for-infernece*]
    (binding [*local-conjunctive-rexprs-for-infernece* (lazy-cat conjuncts-existsing
                                                                 conjuncts)]
      (cond (instance? jit-local-variable-rexpr V)
            (let [r (simplify R)]
              (when-not (= R r)

                (if (or (is-bound-jit? V)
                        (is-empty-rexpr? r))
                  r
                  (do (dyna-assert (contains? (exposed-variables r) V))
                      (make-proj V r)))))

            (instance? jit-hidden-variable-rexpr V)
            (let [r (simplify R)]
              (when-not (= R r)
                (debug-repl "proj hidden var result")
                (???)))

            :else
            (???)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ^{:private true :dynamic true} *jit-aggregator-info*)

(defn- aggregator-out-var []
  (when-not (bound? #'*jit-aggregator-info*)
    (debug-repl "agg out not bound"))
  (if (:out-var @*jit-aggregator-info*)
    (:out-var @*jit-aggregator-info*)
    (let []
      (assert (can-generate-code?))
      (if (contains? @*jit-aggregator-info* :partial-agg-var)
        (let [p (:partial-agg-var @*jit-aggregator-info*)
              out-var (gensym 'aggoutB)
              prev-vals (jit-evaluate-cljform `(get-value ~p))]
          (assert (instance? jit-exposed-variable-rexpr p))
          (add-to-generation! (fn [inner]
                                `(let* [~out-var (volatile! ~(:cljcode-expr prev-vals))]
                                   ~(inner))))
          (vswap! *jit-aggregator-info* assoc :out-var out-var :current-out-var (volatile! (get-current-value prev-vals)))
          out-var)
        (let [out-var (gensym 'aggoutA)]
          (add-to-generation! (fn [inner]
                                `(let* [~out-var (volatile! nil)]
                                   ~(inner))))
          (vswap! *jit-aggregator-info* assoc :out-var out-var :current-out-var (volatile! nil))
          out-var)))))



(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr Rbody1))
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        Rbody2 (if (is-aggregator-op-partial-result? Rbody1)
                   (:remains Rbody1)
                   Rbody1)]
    (when (and (is-aggregator-op-partial-result? Rbody1)
               (not *jit-compute-unification-failure*))
      (if (contains? @metadata :group-vars)
        (assert (= (:group-vars Rbody1) (@metadata :group-vars)))
        (vswap! metadata assoc :group-vars (:group-vars Rbody1)))
      (vswap! metadata assoc :partial-agg-var (:partial-var Rbody1)))
    (vswap! metadata assoc :operator operator)
    #_(when (can-generate-code?)
      (when (nil? (:current-out-var @metadata))
        (vswap! metadata assoc :current-out-var (volatile! nil)))
      (when-not (contains? @metadata :group-vars)
        (vswap! metadata assoc :group-vars (vec (remove is-bound-jit? (exposed-variables Rbody2))))))

    (binding [*jit-aggregator-info* metadata]
      (vswap! *jit-simplify-call-counter* inc)
      (when (is-empty-rexpr? Rbody2)
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    {:runtime-checks []
                                                     :matching-vars []
                                                     :simplify-call-counter @*jit-simplify-call-counter*
                                                     :aggregator-assign-value true
                                                     :kw-args {:agg-final true}}]))
      (if (*jit-simplify-rewrites-picked-to-run* {:runtime-checks []
                                                  :matching-vars []
                                                  :simplify-call-counter @*jit-simplify-call-counter*
                                                  :aggregator-assign-value true
                                                  :kw-args {:agg-final true}})
            (if *jit-compute-unification-failure*
              (make-multiplicity 0)
              (let [] ;; this is the rewrite which assigns the value to the output
                (assert (can-generate-code?))
                (assert (empty? (:group-vars @metadata))) ;; TODO
                (when (is-aggregator-op-partial-result? Rbody1)
                  ;; make sure that this is loaded
                  (aggregator-out-var))
                (if (contains? @metadata :out-var)
                  (let [path (map jit-evaluate-cljform (:group-vars @metadata))
                        agg-var `(deref ~(aggregator-out-var))
                        agg-get (if (empty? path) agg-var `(get-in ~agg-var [~@(map #(list 'get-value %) (:group-vars @metadata))]))
                        agg-lower `((. ~(with-meta (symbol "dyna.rexpr-aggregators" (str "defined-aggregator-" (:name operator)))
                                          {:tag "dyna.rexpr_aggregators.Aggregator"})
                                       ~'lower-value)
                                    ~agg-get)
                        agg-out-var (gensym 'agg-out-value)
                        agg-current (if (empty? path)
                                      @(:current-out-var @metadata)
                                      (get-in @(:current-out-var @metadata) (map get-current-value path)))
                        ]
                    ;(debug-repl "pick agg out lower")
                    (add-to-generation! (fn [inner]
                                          `(let [~agg-out-var ~agg-lower]
                                             ;(debug-repl "jitted agg out")
                                             (when (nil? ~agg-out-var)
                                               (throw (UnificationFailure. "aggregator is over nothing")))
                                             ~(inner))))
                    (jit-evaluate-cljform `(set-value! ~result-variable ~{:type :value
                                                                          :cljcode-expr agg-out-var
                                                                          :current-value (if (nil? agg-current) ;; if the current value is nil, then that means that nothing was aggregated, which would just be the unification failure case.  However, we are going to generate assuming that something will be returned.  Hence, we will just fill in the dummy value of 0 for this
                                                                                           0
                                                                                           agg-current)}))
                    (make-multiplicity 1))
                  (make-multiplicity 0))
                ))
            (let [group-vars (:group-vars @metadata) ;; if the aggregator rewrite was not picked to run
                  body (simplify Rbody2)]
              (if (and (= body Rbody2) (nil? (:out-var @metadata)))
                nil
                (if (and (is-empty-rexpr? body) (empty? (:group-vars @metadata)) (not (contains? @metadata :out-var)))
                  (make-multiplicity 0)
                  (do
                    ;; this is some partially evaluated expression, which will then have to figure out if there is something which could
                    (if (and (not (contains? @metadata :out-var)) (not (is-aggregator-op-partial-result? Rbody1)))
                      (make-no-simp-aggregator-op-outer operator result-variable body)
                      (let [outvar (aggregator-out-var)
                            ret-body (make-no-simp-aggregator-op-partial-result (jit-expression-variable-rexpr. `(deref ~outvar))
                                                                                group-vars
                                                                                body)
                            ret (make-no-simp-aggregator-op-outer operator
                                                                  result-variable
                                                                  ret-body)
                            ]
                        ret))))))))))

;; (defn- agg-inner-value-handle-context [rexpr incoming-variable])
;; (defn- agg-inner-value-handle-jit [rexpr incoming-variable]
;;   )

(def-rewrite
  :match (aggregator-op-inner operator (:any incoming) (:any-list projected-vars) (:rexpr R))
  :run-at :jit-compiler
  (do
    (vswap! *jit-simplify-call-counter* inc)
    (let [metadata (jit-metadata)
          self-id {:runtime-checks []
                   :matching-vars []
                   :simplify-call-counter @*jit-simplify-call-counter*
                   :aggregator-pass-value true
                   :kw-args {:agg-inner true}}
          iters (binding [*jit-variable-types-work-normally* true ;; make it so that we can use the existing find iterator code with jit var placeholders
                          *jit-generate-functions* (if (nil? *jit-generate-functions*) nil ())]
                  (find-iterators R))]
      (if (is-multiplicity? R)
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    self-id])
        (when-not (empty? iters)
          (let [conj-iterator (iterators/make-conjunction-iterator iters)
                what-bound (iter-what-variables-bound conj-iterator)
                bound-order (iter-variable-binding-order conj-iterator)]
            ;(debug-repl "has iters")
            (when-not (empty? what-bound) ;; if there is nothing bound, then the iterator is not useful
              (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                          (assoc-in self-id [:kw-args :aggregator-iterators] true)])))))
      (let [body (simplify R)]
        (cond (*jit-simplify-rewrites-picked-to-run* self-id)
              (if *jit-compute-unification-failure*
                (make-multiplicity 0)
                (let [ ;; vvv (when-not (is-bound-jit? incoming)
                       ;;       (debug-repl "incoming"))
                      incoming-val (jit-evaluate-cljform `(get-value ~incoming))
                      local-agg (bound? #'*jit-aggregator-info*)]
                  (assert (can-generate-code?))
                  (assert (and (is-multiplicity? body) (= 1 (:mult body)))) ;; TODO: this needs to handle higher mult
                  (if local-agg
                    (let [out-var (aggregator-out-var)
                          combine-fn (jit-evaluate-cljform `(. ~operator combine-ignore-nil))
                          path (map jit-evaluate-cljform (:group-vars @*jit-aggregator-info*))
                          ]
                      (add-to-generation!
                       (if (empty? path)
                         `(vswap! ~out-var ~(:cljcode-expr combine-fn) ~(:cljcode-expr incoming-val))
                         `(vswap! ~out-var update-in [~@(map :cljcode-expr path)]
                                  ~(:cljcode-expr combine-fn) ~(:cljcode-expr incoming-val))))
                      (if (empty? path)
                        (vswap! (:current-out-var @*jit-aggregator-info*) (. operator combine-ignore-nil) (get-current-value incoming-val))
                        (vswap! (:current-out-var @*jit-aggregator-info*) update-in (map get-current-value path)
                                (. operator combine-ignore-nil)
                                (get-current-value incoming-val)))
                      (make-multiplicity 0) ;; this aggregator is done, so we just return the aggregator with value zero
                      )
                    (let [agg-contrib-result (gensym 'agg-contrib-res)]
                      ;; any binding to external variables will have to be set into the context
                      ;; but that should already have happened.  If there is something which might have that this will
                      ;; result in some of the values will work with it find that there
                      ;; the path value will also have to become set

                      ;; if there are some values
                      #_(when *jit-inside-disjunct*
                        (debug-repl "need to handle assignments inside of disjunct")
                        (???))
                      (assert (is-multiplicity? body))
                      (add-to-generation!
                       (fn [inner]
                         `(let [~agg-contrib-result ((tlocal aggregator-op-contribute-value) ~(:cljcode-expr incoming-val) ~(:mult body))]
                            ;; if this is a non-empty R-expr, then we are going to have to handle this via some other mechnism.
                            ;; I suppose that this could become a hole, in which case it would likely become a zero value
                            (assert (is-empty-rexpr? ~agg-contrib-result)) ;; if there are external variables, those need to get aligned here
                            ~(inner)
                            )))
                      ;; this can have that some R-expr will get returned, in which case it will have to handle the returned value

                                        ;(debug-repl "value pass for external call")
                      (let [r (make-jit-placeholder nil agg-contrib-result (vec (exposed-variables rexpr)))
                            rm (jit-metadata r)]
                        ;; just assume that the result is zero, in which case there would be nothing to do here.  This will realistically
                        (vswap! rm assoc :current-rexpr (make-multiplicity 0))
                        r)))))

              (and (not (empty? iters)) (*jit-simplify-rewrites-picked-to-run* (assoc-in self-id [:kw-args :aggregator-iterators] true)))
              (if *jit-compute-unification-failure*
                (make-multiplicity 0)
                ;; TODO: we should check that there is some variable that can be bounded by some iterator before we start running it, otherwise
                ;; it is going to potentially have that the iterator will create something which might not work out
                (let [inner-body (if (is-jit-run-iterator? body) ;; we can always choose to ignore an iterator
                                   (:body body)
                                   body)

                      find-iter-var (gensym 'find-iter)
                      conj-iter-var (gensym 'conj-iter)
                      diterator-var (gensym 'diterator)
                      hole-rexpr-var (gensym 'iter-hole)

                      conj-iterator (iterators/make-conjunction-iterator iters)
                      what-bound (iter-what-variables-bound conj-iterator)
                      bound-order (iter-variable-binding-order conj-iterator)

                      picked-bound-order (first bound-order)


                      find-iter-cljcode (find-iterators-cljcode body)

                      new-body (make-jit-run-iterator (jit-expression-variable-rexpr. diterator-var)
                                                      (vec picked-bound-order)
                                                      (vec (map #(contains? what-bound %) picked-bound-order))
                                                      inner-body)
                      new-self (make-no-simp-aggregator-op-inner operator incoming projected-vars new-body)

                      body-exposed (exposed-variables body)
                      new-with-iter-cljcode (generate-cljcode-to-materalize-rexpr new-self
                                                                                  :simplify-result false
                                                                                  :attempt-variable-read-values true)
                      ;zzz (debug-repl "zz" false) ;;
                                        ;inner-body-rexpr-cljcode (generate-cljcode-to-materalize-rexpr body :simplify-result false)
                      ;; If there is some variable which is local variable, then it might be that this can not project that in
                      ;; this representation, as this a fractional part of the R-expr.  So I suppose that this is similar to the constraints
                      ;; of the R-expr to when the iterator currently runs, which is when all of the variables are bound

                      ]
                  (add-to-generation! (fn [inner]
                                        `(let [~find-iter-var ~find-iter-cljcode]
                                           (when (empty? ~find-iter-var)
                                             ;; if there are no iterators, then this rewrite will not work
                                             (throw (DynaJITRuntimeCheckFailed.)))
                                           (let [~conj-iter-var (iterators/make-conjunction-iterator ~find-iter-var)]
                                             ;; we are going to have to start the iterator.  This means checking that the iterator matches what we expect and supports what we want
                                             (when-not (subset? ~what-bound (iter-what-variables-bound ~conj-iter-var))
                                               (throw (DynaJITRuntimeCheckFailed.)))
                                             (let [~diterator-var (try (iter-create-iterator ~conj-iter-var ~picked-bound-order)
                                                                       (catch IteratorBadBindingOrder ~'_
                                                                         (throw (DynaJITRuntimeCheckFailed.))))]
                                               (when (nil? ~diterator-var)
                                                 (throw (DynaJITRuntimeCheckFailed.)))
                                               ;(debug-repl "before hole value")
                                               (let [~hole-rexpr-var ~(:cljcode-expr new-with-iter-cljcode)]

                                                 ~(inner)))))))
                  ;; this is going to have to get the iterators from the object.  But we are going to have to figure out which variables
                  ;; we can iterate.  It might be that we already want to have to decied that when the variables
                  ;; which can be bound are decied.  But if there are multiple nested iterators, then we want to figure out
                  ;; which of them can actually work

                  ;; this should take the body, and generate some R-expr wihch can then represent the steps which will happen when it binds to particular values

                  ;; the order in which the variables can be bound should consider which of the


                  (let [ret (make-jit-placeholder nil hole-rexpr-var (vec (exposed-variables rexpr)))
                        md (jit-metadata ret)]
                    (vswap! md assoc :current-rexpr (:rexpr-type new-with-iter-cljcode))
                    ;(debug-repl "choose to run iterator" false)
                    ret)))


              :else
              (if (is-empty-rexpr? body)
                body
                (do
                  (make-no-simp-aggregator-op-inner operator incoming projected-vars body))))))))

#_(def-rewrite
  :match (aggregator-op-inner operator (:any incoming) (:any-list projected-vars) (:rexpr R))
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        body (simplify R)]
    (if (and (= R body) (not (is-bound-jit? incoming)))
      nil ;; there is nothing rewritten/bound, so we just let this stuff continue
      (if (is-empty-rexpr? body)
        (do
          (when *jit-compute-unification-failure*
            (vswap! metadata assoc :unification-failure-empty true))
          body)
        (do
          (when *jit-compute-unification-failure*
            (vswap! metadata assoc :unification-failure-empty false))

          )))
    ))

#_(def-rewrite
  :match (aggregator-op-inner operator (:any incoming) (:any-list projected-vars) (:rexpr R))
  :run-at :jit-compiler
  (let [body (simplify R)]
    (if (and (= body R) (not (is-bound-jit? incoming)))
      nil ;; then there was nothing rewritten/bound, so we can just let stuff continue
      (if (is-empty-rexpr? body)
        body
        (if (is-multiplicity? body)
          (let [out-var (aggregator-out-var)
                incoming-val (jit-evaluate-cljform `(get-value ~incoming))
                combine-fn (jit-evaluate-cljform `(. ~operator combine-ignore-nil))]
            (assert (= body (make-multiplicity 1))) ;; TODO handle other mults here, this is going to have to contribute more than once
            (if (empty? (:group-vars @*jit-aggregator-info*))
              (do
                (add-to-generation! `(vswap! ~out-var ~(:cljcode-expr combine-fn) ~(:cljcode-expr incoming-val)))
                (vswap! (:current-out-var @*jit-aggregator-info*)
                        (. operator combine-ignore-nil)
                        (get-current-value incoming-val)))
              (let [path (map jit-evaluate-cljform (:group-vars @*jit-aggregator-info*))]
                (add-to-generation! `(vswap! ~out-var update-in [~@(map :cljcode-expr path)]
                                             ~(:cljcode-expr combine-fn) ~(:cljcode-expr incoming-val)))
                (vswap! (:current-out-var @*jit-aggregator-info*)
                        update-in
                        (map :current-value path)
                        (. operator combine-ignore-nil)
                        (get-current-value incoming-val)))) ;; TODO this needs to handle the different values for this
                                        ;(debug-repl "handle jit agg op inner")
            (make-multiplicity 0) ;; this has already been handled, so we can remove it from the R-expr
            )
          (let [ret (make-no-simp-aggregator-op-inner operator incoming projected-vars body)]
                                        ;(debug-repl "more to do in aggregator")
            ret))))))

;; if there are no more varibles to bind, then we can just delete the run-iterator operation from the R-expr
(def-rewrite
  :match (jit-run-iterator iterator (empty? iterator-order) iterator-variables-bound body)
  :run-at :construction
  body)

(def-rewrite
  :match (jit-run-iterator iterator iterator-order iterator-variables-bound body)
  :run-at :jit-compiler
  (do
    (vswap! *jit-simplify-call-counter* inc)
    (let [iter-bind-variables-id {:runtime-checks []
                                  :matching-vars []
                                  :simplify-call-counter @*jit-simplify-call-counter*
                                  :kw-args {:iterator-bind-variables true}}
          new-body (simplify body)]
      (when (is-bound-jit? (first iterator-order))
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    iter-bind-variables-id]))

      (if (*jit-simplify-rewrites-picked-to-run* iter-bind-variables-id)
        (if *jit-compute-unification-failure*
              (make-multiplicity 0)
              (let [iter-value (jit-evaluate-cljform `(get-value ~iterator))
                    var-value (jit-evaluate-cljform `(get-value ~(first iterator-order)))
                    new-iter-name (gensym 'new-iter-bound)]

                ;(debug-repl "make iter variable bound")

                (add-to-generation! (fn [inner]
                                      `(let [~new-iter-name (iter-bind-value ~(:cljcode-expr iter-value) ~(:cljcode-expr var-value))]
                                         (when (nil? ~new-iter-name)
                                           (throw (UnificationFailure. "JIT iter binding failed")))
                                         ~(inner))))

                (make-jit-run-iterator (jit-expression-variable-rexpr. new-iter-name) (rest iterator-order) (rest iterator-variables-bound) new-body)))

        (make-jit-run-iterator iterator iterator-order iterator-variables-bound new-body)))))

(def-rewrite
  :match (aggregator-op-inner operator (:any incoming) (:any-list projected-vars)
                              (jit-run-iterator iterator iterator-order iterator-variables-bound (:rexpr Rbody)))
  :run-at :jit-compiler
  (do
    (vswap! *jit-simplify-call-counter* inc)
    (let [run-iter-rewrite-id {:runtime-checks []
                               :matching-vars []
                               :simplify-call-counter @*jit-simplify-call-counter*
                               :kw-args {:iterator-run true}}]
      (when (and (not (is-bound-jit? (first iterator-order)))
                 (first iterator-variables-bound))
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    run-iter-rewrite-id]))
      (when (*jit-simplify-rewrites-picked-to-run* run-iter-rewrite-id)
        (if *jit-compute-unification-failure*
          (make-multiplicity 0)
          (let [iter-val (jit-evaluate-cljform `(get-value ~iterator))
                iter-binding (gensym 'iter-binding)
                iter-run-result (gensym 'iter-run-result)
                iter-jhole-result (gensym 'iter-jithole)

                getting-bound (first iterator-order)
                bound-value (jit-expression-variable-rexpr. `(iter-variable-value ~iter-binding))


                new-body (make-jit-run-iterator (jit-expression-variable-rexpr. `(iter-continuation ~iter-binding))
                                                                                  (vec (rest iterator-order))
                                                                                  (vec (rest iterator-variables-bound))
                                                                                  (remap-variables Rbody {getting-bound bound-value}))
                ;; new-self (if (= incoming getting-bound)
                ;;            (make-no-simp-aggregator-op-inner operator
                ;;                                              incoming
                ;;                                              (vec (remove #{getting-bound} projected-vars))
                ;;                                              (make-conjunct [(make-no-simp-unify incoming bound-value) ;; this unify is a "hack" as we need the bound value to be exposed, henced it will get set into the state of the generated R-expr.  Currently the incoming is projected out from being exposed, and not subsuited.  Not sure if this is going to be a problem elsewhere when the JIT is generating code...
                ;;                                                              new-body]))
                ;;            (make-no-simp-aggregator-op-inner operator
                ;;                                              incoming
                ;;                                              (vec (remove #{getting-bound} projected-vars))
                ;;                                              new-body))

                new-self (make-no-simp-aggregator-op-inner operator
                                                           (if (= incoming getting-bound) bound-value incoming)
                                                           (vec (remove #{getting-bound} projected-vars))
                                                           new-body)

                ;rr (debug-repl "rr")

                new-self-cljcode (generate-cljcode-to-materalize-rexpr new-self
                                                                       :simplify-result false
                                                                       :attempt-variable-read-values true)
                ]
            ;(debug-repl "new self cljcode" false)

            ;; this is going to construct a sub-rexpr and then run the iterator and simplification.  The hole will become a disjunct
            ;; of all the resulting R-exprs.  Ideally the hole should become filled with R-exprs which correspond with 0-mult.  In which case the
            ;; inner body of the iterator will have been run completely

            ;; the only variables which might have some ground value will get that it might be represented with some value
            ;; if something will have that this

            (assert (not (bound? #'*jit-aggregator-info*)))
            (assert (not (contains? (exposed-variables (:rexpr-type new-self-cljcode)) getting-bound))) ;; the getting bound variable will be passed directly, so we do not need to create something for the context of htis

            (add-to-generation! (fn [inner]
                                  `(let [~iter-jhole-result
                                         (let [~iter-run-result (transient [])
                                               ;; going to create a map of all of the variables that are bound in the context
                                               ;; and then we can extend
                                               ;; base-context-binding# (assoc {}
                                               ;;                              ~@(apply concat ))
                                               ;;iter-run-log# (transient [])
                                               ]
                                           (doseq [~iter-binding (iter-run-iterable ~(:cljcode-expr iter-val))]
                                             (system/should-stop-processing?)
                                             (let [new-r# ~(:cljcode-expr new-self-cljcode)
                                                   nested-context# (context/make-context-jit new-r# {}) ;; we should not need to add any variables here as everything will just get passed as constant values into the new-r above
                                                   result-r# (context/bind-context nested-context#
                                                                                   (try (~'simplify new-r#)
                                                                                        (catch UnificationFailure ~'_ (make-multiplicity 0))))]
                                               (when-not (is-empty-rexpr? result-r#)
                                                 (conj! ~iter-run-result result-r#))
                                        ;(conj! iter-run-log# [new-r# nested-context# result-r# ~iter-binding])
                                               ))
                                           ;(debug-repl "after ran iterator")
                                           (let [r# (persistent! ~iter-run-result)]
                                             (if (empty? r#)
                                               (make-multiplicity 0)
                                               (make-disjunct r#))))]
                                     ~(inner))))

            (let [ret (make-jit-placeholder nil iter-jhole-result (vec (exposed-variables rexpr)))
                  md (jit-metadata ret)]
              (vswap! md assoc :current-rexpr (make-multiplicity 0)) ;; this should just become a zero as we are hoping that it will internally fully run all of the loops
              ;(debug-repl "run iterator with aggregator")
              ret)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (disjunct (:rexpr-list children))
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        ex-child (map exposed-variables children)
        exposed (apply union ex-child)
        ;;handle-disjunct (remove is-bound-jit? exposed) ;; anything that is bound externally does not need to be handled by the disjunct
        ret-children (transient [])
        parent-variable-name-bindings *local-variable-names-for-variable-values*
        changed (volatile! false)]
    #_(when (contains? @metadata :disjunct-bindings)
        (debug-repl "handle disjunct bindings"))

    (doseq [[c prev-bind] (zipseq-longest children (:disjunct-bindings @metadata))]
      (let [new-binding (volatile! @parent-variable-name-bindings)]
        (doseq [[k v] prev-bind
                :when (not= (@new-binding k) v)]
          (if (nil? (@new-binding k))
            (vswap! new-binding assoc k v)
            (do (debug-repl "handle diff value")
                (???))))
        (let [r (binding [*local-variable-names-for-variable-values* new-binding
                          *jit-inside-disjunct* true]
                  (simplify c))]
          (when (or (not= r c) (not= @new-binding @parent-variable-name-bindings))
            (vreset! changed true))
          (doseq [[v b] @new-binding
                  :when (not= (get @parent-variable-name-bindings v) b)]
            (dyna-assert (not (contains? @parent-variable-name-bindings v)))
            (when (:bound-from-outer-context b) ;; this is just caching the value into a local variable somewhere, so this is always fine
              (vswap! parent-variable-name-bindings assoc v b)))
          (when-not (is-empty-rexpr? r)
            (conj! ret-children [r @new-binding])))))
    (when @changed
      (let [ret (persistent! ret-children)
            bindings (map second (remove #(is-empty-rexpr? (first %)) ret))
            retd (vec (remove is-empty-rexpr? (map first ret)))]
        (case (count retd)
          0 (make-multiplicity 0)
          1 (do
              (vswap! *local-variable-names-for-variable-values* merge (first bindings))
              (first retd))
          (do
            (when-not *jit-compute-unification-failure*
              (vswap! metadata assoc :disjunct-bindings bindings))
            (make-no-simp-disjunct retd)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(def-rewrite
  :match (simple-function-call (:unchecked function) (:any result) (:ground-var-list arguments))
  :run-at :jit-compiler
  (do
    ;; TODO: this should generate something in the output code which will just
    ;; call the function directly.  It will want to do something like evaluate
    ;; the value of all of the arguments I suppose that jit-evaluate-cljform
    ;; should allow for a function or some value directly (like a placeholder)
    ;; in which case, it would have to translate it into what the expression would look like when it

    (???)
    (add-to-generation!
     (jit-evaluate-cljform `(set-value! ~result (~function ~@(map #(list 'get-value %) arguments)))))
    (make-multiplicity 1)))


(def-rewrite
  :match (jit-placeholder _ _ _)
  :run-at :standard
  (do
    (debug-repl "should not happen, attempting to simplify jit-placeholder")
    (???)))

(def-rewrite
  :match (jit-placeholder _ _ placeholder-vars)
  :run-at :construction
  :is-check-rewrite true
  (do
    (dyna-assert (not (some is-constant? placeholder-vars)))
    nil))

(def-rewrite
  :match (jit-placeholder external-name local-name placeholder-vars)
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        current-value (if-not (nil? external-name)
                        ((keyword external-name) *jit-generating-rewrite-for-rexpr*)
                        (strict-get @metadata :current-rexpr))
        current-cljcode (if-not (nil? external-name)
                          `(. ~(with-meta 'rexpr {:tag (jit-generating-rewrite-for-rexpr-type)}) ~external-name)
                          local-name)
        rewrite-sig {:runtime-checks []
                     :matching-vars []
                     :simplify-call-counter @*jit-simplify-call-counter*
                     :kw-args {:jit-placeholder true}}]
    (vswap! *jit-simplify-call-counter* inc)
    (when (and *jit-call-simplify-on-placeholders* (not (:simplify-fixed-pointed @metadata false)))
      (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                  rewrite-sig])
      (when (and (can-generate-code?)
                 (bound? #'*jit-aggregator-info*))
        ;; make sure the out var is pre populated, otherwise this is going to have that this will result in nothing
        (aggregator-out-var)))
    (let [hole-jinfo (rexpr-jit-info current-value)]
      (when (and *jit-consider-expanding-placeholders* ;; if the placeholder is something that we are willing to embed into the R-expr
                 (>= (:num-simplifies-done @metadata 0) 1)
                 (if (contains? hole-jinfo :generated-name)
                   ;; if this is a JITted expression, then we just need to check if tihs does not have something that needs to run an iterator, as that can do lots of expansion
                   (not (some is-jit-run-iterator? (all-conjunctive-rexprs (:prim-rexpr hole-jinfo))))

                   ;; if not JITted, just make sure that this is a "simple" R-expr without more nested values
                   (and (not (is-composit-rexpr? current-value))  ;; we will embed things which do not have recursive nested R-exprs.
                        (not (is-user-call? current-value)))))
        ;; then we have already done one rewrite, and the current nested R-expr is a JIT type.  This means that we can merge the two JIT type R-exprs together
        ;; the reason that we are oging to check if the rewrite
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    (assoc rewrite-sig :jit-hole-embed true)])))

    (cond
      (*jit-simplify-rewrites-picked-to-run* rewrite-sig)
      (if *jit-compute-unification-failure*
        (make-multiplicity 0)
        (let [agg-out-var (when (bound? #'*jit-aggregator-info*)
                            (aggregator-out-var))
              vars (doall (for [k placeholder-vars
                                :let [kv (jit-evaluate-cljform k)
                                      bv (is-bound-jit? k)]]
                            (merge {:var k
                                    :clj-var kv
                                    :bound bv}
                                   (when bv
                                     (let [cv (jit-evaluate-cljform `(get-value ~k))]
                                       {:current-value-clj cv
                                        :current-value (get-current-value cv)})))))
                                        ;values-map (into {} )
              nested-context-var (gensym 'nested-context)
              new-local-name (gensym 'new-hole-rexpr)
              expanding-placeholder *jit-consider-expanding-placeholders*
              ctx-values (into {} (for [v vars]
                                    [(get-current-value (:clj-var v)) (:current-value v)]))
              ctx (context/make-context-jit current-value ctx-values)
              rewritten-rexpr (context/bind-context-raw ctx
                                                        (try
                                                          ;; TODO: this should call different simplify methods depending on which kind of simplify we are perfoming
                                                          ;; but in the case that it is inference, then it will need some information about the calling context
                                                          ;; which is expensive information to "create" at runtime and pass along....
                                                          (simplify-fast current-value)
                                                          (catch UnificationFailure _ (make-multiplicity 0))))

              aggregator-func-bindings (when (bound? #'*jit-aggregator-info*)
                                         (let [agg-path (doall
                                                         (for [v (:group-vars @*jit-aggregator-info*)]
                                                           (???) ;; This is going to have to handle already bound values from the local context
                                                           ;; and also get values from the context in the case that it could be assigned elsewhere
                                                           ))
                                        ;out-var (aggregator-out-var)
                                               op (with-meta (symbol "dyna.rexpr-aggregators" (str "defined-aggregator-"
                                                                                                   (:name (strict-get @*jit-aggregator-info* :operator))))
                                                    {:tag "dyna.rexpr_aggregators.Aggregator"})]
                                           ['aggregator-op-contribute-value `(fn [~'incoming-value ~'mult]
                                                                               (let [^RContext ~'**context** (ContextHandle/get) ;; going to reget the context, as it might have changed in the nested context, so we will still be able to get the new variable values
                                                                                     ~'path [~@agg-path]
                                                                                     ]
                                                                                 (vswap! ~agg-out-var
                                                                                         ~@(when-not (empty? agg-path)
                                                                                             `[update-in ~'path])
                                                                                         (. ~op combine-ignore-nil)
                                                                                         ((. ~op many-items) ~'incoming-value ~'mult))
                                        ;(debug-repl "jit contribute value fun")
                                                                                 (make-multiplicity 0) ;; this has incoperated the value, s we record a zero R-expr
                                                                                 ))
                                            'aggregator-op-additional-constraints `(constantly (make-multiplicity 1))
                                            'aggregator-op-saturated `(constantly false)
                                            ])
                                         )
              ]
          (assert (can-generate-code?))
          (vswap! metadata update :num-simplifies-done (fnil inc 0))
          (vswap! metadata assoc
                  :simplify-fixed-pointed (= rewritten-rexpr current-value)
                  :current-rexpr rewritten-rexpr)
          ;(debug-repl "do jit placeholder rewrite" false)
          (add-to-generation! (fn [inner]
                                `(let [~nested-context-var (context/make-context-jit ~current-cljcode
                                                                                     ;; using assoc here instead of a map {} because it is possible
                                                                                     ;; that a variable will be repeated
                                                                                     (assoc-make-binding-map
                                                                                      ~@(apply concat
                                                                                               (for [v vars
                                                                                                     :when (:bound v)]
                                                                                                 [(:cljcode-expr (:clj-var v))
                                                                                                  (:cljcode-expr (:current-value-clj v))]))))
                                       ~new-local-name (tbinding-with-var ~'**threadvar**
                                                                          [ ;; this will need to have aggregators get set here
                                                                           ~@aggregator-func-bindings
                                                                           ]
                                                                          (context/bind-context ~nested-context-var
                                                                                                (~'simplify ~current-cljcode)))]
                                   ;(debug-repl "after placeholder simplify inner" false)
                                   (when (is-empty-rexpr? ~new-local-name) ;; if this is expected to get zero, then we might not have something here?
                                     ;; or we might track if the result is zero, in which case it would have something else.
                                     (throw (UnificationFailure. "JIT nested simplify got zero")))
                                   ~(inner)
                                   )))

          (make-jit-placeholder nil new-local-name placeholder-vars)))


      (*jit-simplify-rewrites-picked-to-run* (assoc rewrite-sig
                                                    :jit-hole-embed true))
      (if *jit-compute-unification-failure*
        (make-multiplicity 0)
        (let []
          ;; the R-expr which gets embedded, will have to figure out which of the expressions might
          (add-to-generation! (fn [inner]
                                `(do
                                   ;; first check that the type of the expressionmatches what we are expecting
                                   (when-not (instance? ~(type current-value) ~current-cljcode)
                                     (throw (DynaJITRuntimeCheckFailed.)))
                                   (let [] ;; this is going to have to expand all of the local variable names.
                                     (???))
                                   )))
          (debug-repl "going to embed nested R-expr")
          ;; this is going to have to do a type check, and then
          (???)))

      :else nil ;; then we are not doing any rewrite
      )))


#_(def-rewrite
  :match (conjunct (:rexpr-list children))
  :run-at :jit-compiler
  (make-conjunct (vec (map simplify children))))

;; there needs to be something which tracks the current conjuncts.  I suppose
;; this means that anytime that it goes down into some expression where the
;; conjunct might change, then it



#_(def-rewrite
    :match (jit-disjunct (:rexpr-list children))
    :run-at :jit-compiler
    )
