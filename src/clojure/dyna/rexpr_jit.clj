(ns dyna.rexpr-jit
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr-constructors])
  (:import [dyna.rexpr proj-rexpr]))

;; this is going to want to cache the R-expr when there are no arguments which are "variables"
;; so something like multiplicy can be just a constant value


;; map from the name of the jitted rexpr -> to the metadata which was used during construction
(def rexprs-types-constructed (atom {}))

(def rexpr-rewrites-constructed (atom #{}))

;; a map from an R-expr to a jitted rexpr
(def rexprs-map-to-jit (atom {}))

(def rexpr-convert-to-jit-functions (atom {}))


(def ^:dynamic *jit-current-compilation-unit* {})  ;; there needs to be some
                                                   ;; information here which
                                                   ;; represents the current
                                                   ;; compilation unit.

(def ^:dynamic *jit-get-variable*) ;; will be a function that can be called to get information about the flags, mode.

;; (def ^:dynamic *jit-generate-clojure-code* (volatile! nil))  ;; a volatile which
;;                                                              ;; is a pointer to
;;                                                              ;; a function which
;;                                                              ;; will return the
;;                                                              ;; generated
;;                                                              ;; clojure code up
;;                                                              ;; to this point

(def ^:dynamic *jit-generate-functions* nil)

(defn- add-to-generation! [func]
  (conj! *jit-generate-functions* func))

(defn- generate-cljcode [generate-functions]
  (if (empty? generate-functions)
    identity  ;; I suppose that this could just call its argument
    (let [f (first generate-functions)
          r (generate-cljcode (rest generate-functions))]
      (fn [inner] (f (partial r inner))))))

(defrecord jit-local-variable-rexpr [local-var-symbol]
  RexprValue
  (get-value [this] (???))
  (get-value-in-context [this ctx] (???))
  (set-value! [this value] (???))
  (is-bound? [this] true)
  (is-bound-in-context? [this ctx] true)
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    (???))
  Object
  (toString [this] (str "(jit-local-variable " local-var-symbol ")")))

(defmethod print-method jit-local-variable-rexpr [^jit-local-variable-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))

(defn- generate-cljcode-assign-value [variable value-expression]
  ;; variable should be some rexpr variable, and value-expression is a symbol of a local variable or a constant
  (cond (is-constant? variable)
        `(if (not= ~value-expression (quote ~(get-value variable)))
           (throw (UnificationFailure.)))
        (instance? jit-local-variable-rexpr variable)
        `(if (not= ~value-expression ~(.local-var-symbol variable))
           (throw (UnificationFailure.)))
        (is-variable? variable)
        (let [vinfo (*jit-get-variable* variable)]
          ((:assign-func-cljcode vinfo) value-expression))
        :else (do (debug-repl "???")
                  (???))))


;; (defn delete-rexpr-type [rexpr-name]
;;   (???) ;; there should be something whic hcould be used to delete an R-expr.
;;         ;; though if we are deleting the construction functions, then that might
;;         ;; cause other expressions to break elsewhere.... so not sure how well
;;         ;; this would work an practice
;;   )


;; the iterables should be something like which variables and their orders can be
(def-base-rexpr jit-placeholder [:unchecked placeholder-id
                                 :var-list placeholder-vars
                                 :unchecked placeholder-iterables]) ;; which things are iterable will probably need more information about the iterators, or maybe just don't support having iterators be outside of the JIT expression.  Though I suppose that this is likely to happen in the case that there is a disjunct/memoized expression.  Those are things we we do not want to handle.  So there might be a lot of stuff which is not going to get handled directly....sigh

(defn convert-rexpr-to-placeholder [rexpr]
  (let [iters (find-iterators rexpr)]
    (make-jit-placeholder (gensym 'rexpr-placeholder)
                          (vec (exposed-variables rexpr))

                          iters; (???) ;; need to build some representation of which variables could be iterated here.  there might be something
                          ;; about how efficient the different iterators are going to work.  In which case
                          )))

(def-rewrite
  :match (jit-placeholder _ _ _)
  :run-at :standard
  (do
    (debug-repl "should not happen, attempting to simplify jit-placeholder")
    (???)))


(defn- convert-to-primitive-rexpr [rexpr]
  (if (is-jit-placeholder? rexpr)
    rexpr  ;; this is already a placeholder, so this just gets returned
    (rewrite-rexpr-children-no-simp (primitive-rexpr rexpr) convert-to-primitive-rexpr)))

(defn- get-placeholder-rexprs [rexpr]
  (for [c (get-children rexpr)
        z (if (is-jit-placeholder? c) [c] (get-placeholder-rexprs c))]
    z))

(defn get-rexpr-arg-map [rexpr]
  (let [rtype (rexpr-name rexpr)
        signature (get @rexpr-containers-signature rtype)
        args (get-arguments rexpr)]
    (zipmap (map cdar signature) args)))

(defn get-variables-and-path [rexpr]
  (cond (is-proj? rexpr) (let [body-path (get-variables-and-path (:body rexpr))
                               var (:var rexpr)
                               child-uses (some #(contains? (exposed-variables %) var)
                                                (filter is-jit-placeholder? (vals body-path)))]
                           (merge (into {} (for [[path v] body-path]
                                             (if (not= v var)
                                               [(cons :body path) v])))
                                  (if child-uses
                                    {:var {:hidden-var var}})))
        (is-aggregator? rexpr) (???)
        :else
        (let [litems (rexpr-map-function-with-access-path rexpr
                                                          (fn fr [fname ftype val]
                                                            (case ftype
                                                              :rexpr (if (is-jit-placeholder? val)
                                                                       [[(list fname) val]] ;; this is a base case, so we stop
                                                                       ;; then we are going to keep going
                                                                       (for [[path v] (get-variables-and-path val)]
                                                                         [(cons fname path) v]))
                                                              :rexpr-list (do (assert (not (is-jit-placeholder? val)))
                                                                              (for [[i r] (zipseq (range) val)
                                                                                    [rp rr] (fr `(nth ~i) :rexpr r)]
                                                                                [(cons fname rp) rr]))
                                                              :var [[(list fname) val]]
                                                              :value [[(list fname) val]]
                                                              :var-list (for [[i v] (zipseq (range) val)]
                                                                          [(list fname `(nth ~i)) v])
                                                              :var-map (???) ;; this is going to have to use the key for the access path...
                                                              ;:hidden-var [[(list fname) {:hidden-var val}]] ;; unsure what do do with this....???
                                                              (do
                                                                (debug-repl "unsure type required mapping")
                                                                (???)))))]
          (into {} (apply concat (vals litems))))))

(defn get-variables-values-letexpr [root-var vars-path]
  ;; construct the vector arguments of a let expression with something which will be able to return all of the different values
  (let [so-far (transient {})
        gen-code (transient [])
        rec (fn rec [path]
              (if (empty? path)
                root-var
                (if (contains? so-far path)
                  (get so-far path)
                  (let [pv (rec (drop-last path))
                        lvar (gensym 'vlookup)]
                    (conj! gen-code lvar)
                    (conj! gen-code `(-> ~pv ~(last path)))
                    (assoc! so-far path lvar)
                    lvar))))
        ;; vm (for [[k v] vars-path]
        ;;      [k (rec v)])
        vm (map (fn [x] [x (rec x)]) vars-path)
        ]
    [(into {} vm) (persistent! gen-code)]))

(defn synthize-rexpr-cljcode [rexpr]
  ;; this should just generate the required clojure code to convert the rexpr
  ;; (argument) into a single synthic R-expr.  This is not going to evaluate the code and do the conversion

  (let [prim-rexpr (convert-to-primitive-rexpr rexpr)
        exposed-vars (into #{} (filter is-variable? (exposed-variables rexpr)))
        placeholder-rexprs (into #{} (get-placeholder-rexprs rexpr))
        root-rexpr (gensym 'root) ;; the variable which will be the argument for the conversions
        vars-path (get-variables-and-path rexpr)
        [var-access var-gen-code] (get-variables-values-letexpr root-rexpr (keys vars-path))  ;; this might have to handle exceptions which are going to thrown by the
        new-rexpr-name (gensym 'jit-rexpr)
        new-arg-names (merge (into {} (map (fn [v] [v (gensym 'jv)]) exposed-vars))
                             (into {} (map (fn [r] [r (gensym 'jr)]) placeholder-rexprs)))
        new-arg-names-rev (into {} (for [[k v] new-arg-names]
                                     [v k]))
        new-arg-order (vec (vals new-arg-names))

        rexpr-def-expr `(def-base-rexpr ~new-rexpr-name [~@(flatten (for [a new-arg-order
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
                                          (get @dyna.rexpr-jit/rexprs-types-constructed (quote ~new-rexpr-name))))

        conversion-function-expr `(fn [~root-rexpr]
                                   (let ~var-gen-code ;; this is going to get access to all of the
                                     ;; this will check that we have all of the arguments (non-nil) and that the constant values are the same as what we expect
                                     (when (and ~@(for [[vpath val] vars-path]
                                                    (cond (is-constant? val) `(= ~(strict-get var-access vpath) ~val)
                                                          (is-variable? val) `(not (nil? ~(strict-get var-access vpath)))
                                                          (rexpr? val) `(rexpr? ~(strict-get var-access vpath))
                                                          :else (do (debug-repl "zz")
                                                                    (???)))))
                                       (~(symbol (str "make-" new-rexpr-name))
                                        ~@(for [a new-arg-order]
                                            (strict-get var-access
                                                        (strict-get (into {} (for [[k v] vars-path] [v k]))
                                                                    (get new-arg-names-rev a))))))))
        ret {:orig-rexpr rexpr
             :prim-rexpr prim-rexpr
             :generated-name new-rexpr-name
             :make-rexpr-type rexpr-def-expr
             :conversion-function-expr conversion-function-expr
             :variable-name-mapping new-arg-names ;; map from existing-name -> new jit-name
             :variable-order new-arg-order        ;; the order of jit-names as saved in the R-expr

             ;; ;; should the conversion function have that there is some expression.  In the case that it might result in some of
             ;; ;; if there is something which is giong to construct this value, though there might
             ;; :conversion-function-args (fn [& args] (???))

             ;; ;; check that the shape of the R-expr matches the kind of the thing that we can convert into this generated code
             ;; :check-could-be-converted (fn [rexpr] (???))
             }]
    (swap! rexprs-types-constructed assoc new-rexpr-name ret)
    ret))


(defn synthize-rexpr [rexpr]
  (let [is-new (volatile! false)
        rtype (if (contains? @rexprs-map-to-jit rexpr)
                (get @rexprs-map-to-jit rexpr)
                (let [vv (volatile! nil)]
                  (swap! rexprs-map-to-jit (fn [x]
                                             (if (contains? x rexpr)
                                               (do (vreset! is-new false)
                                                   (vreset! vv (get x rexpr))
                                                   x)
                                               (let [v (synthize-rexpr-cljcode rexpr)]
                                                 (vreset! is-new true)
                                                 (vreset! vv v)
                                                 (assoc x rexpr v)))))
                  @vv))]
    (let [convert-fn (if @is-new
                       (do (eval `(do
                                    (ns dyna.rexpr-jit)
                                    ~(:make-rexpr-type rtype)))
                           (let [f (eval (:conversion-function-expr rtype))]
                             (swap! rexpr-convert-to-jit-functions assoc rexpr f)
                             f))
                       (get @rexpr-convert-to-jit-functions rexpr))]
      ;; return the converted rexpr as well as the type information for this expression
      [(convert-fn rexpr) rtype])))

(defn- get-matchers-for-value [val]
  (into [] (map first (filter (fn [[name func]] (func val)) @rexpr-matchers))))

(def ^:private free-variable-matchers (delay (get-matchers-for-value (make-variable (Object.)))))
(def ^:private ground-variable-matchers (delay (get-matchers-for-value (make-constant (Object.)))))


;; (defn- check-matches
;;   ([rexpr matcher already-matched]
;;    (let [rname (rexpr-name rexpr)
;;          args (get-arguments rexpr)
;;          ret (when (= rname (first matcher)) ;; the name on the match expression does not match
;;               )]

;;      ;(debug-repl "ww")
;;      ret))
;;   ([rexpr matcher] (check-matches rexpr matcher {})))

(defn- compute-match
  ([rexpr matcher matched-variables]
   (let [rname (rexpr-name rexpr)
         args (get-arguments rexpr)]
     (when (= rname (first matcher))
       (every? true? (for [[match-expr arg] (zipseq (rest matcher) args)]
                       (cond (= '_ match-expr) true

                             (symbol? match-expr) (do (assert (not (contains? matched-variables match-expr)))
                                                      true)

                             (and (= 2 (count match-expr))
                                  (not (contains? @rexpr-containers-signature (car match-expr)))
                                  (symbol? (cdar match-expr)))
                             (let [match-requires (car match-expr)
                                   var-info (cond (is-constant? arg) {:value arg}
                                                  (is-variable? arg) (*jit-get-variable* arg)
                                                  (instance? jit-local-variable-rexpr arg) {:var-mode @ground-variable-matchers
                                                                                            :local-variable-value (.local-var-symbol ^jit-local-variable-rexpr arg)}
                                                  :else (do (debug-repl "todo") (???)))
                                   match-successful
                                   (cond
                                     (some #{match-requires} (:var-modes var-info [])) true

                                     (and (contains? var-info :value) (contains? @rexpr-matchers match-requires))
                                     ((get @rexpr-matchers match-requires) (:value var-info))

                                     :else (do
                                        ;(debug-repl "qq")
                                             false)
                                     ;; TODO: there may be more more cases which can cause something to match
                                     ;; :else (do (debug-repl "todo2")
                                     ;;           (???))
                                     )]
                               (when match-successful
                                 (assoc! matched-variables (cdar match-expr) (assoc var-info
                                                                                    :rexpr-var arg)))
                               ;(when-not match-successful (debug-repl "rr"))
                               match-successful)


                             :else (do (debug-repl "todo3")
                                       (???))))))))

  ([rexpr matcher]
   (let [m (transient {})
         r (compute-match rexpr matcher m)]
     [r (persistent! m)])))

(defn- compute-rewrite-ranking [rewrite]
  ;; bigger numbers will be perfable rewrites.  Rewrites which directly compute
  ;; a value should be prefered over something which checks for 0 for example.
  (cond (:is-assignment-rewrite (:kw-args rewrite) false) 100
        (:is-check-rewrite (:kw-args rewrite) false) 90
        :else 0))

(defn- is-composit-rexpr? [rexpr]
  ;; meaning that there is some sub-rexprs here, in which case, we might want to constructed
  (some (fn r [x] (or (rexpr? x)
                      (and (seqable? x) (some r x))))
        (get-arguments rexpr)))

(defn- make-rexpr-type-in-jit [construct-func]
  (fn [& args]
    ;; this will allow us to intercept which functions are called when it is
    ;; doing the construction
    (apply construct-func args)))

(defn- make-cljcode-to-make-rexpr [r]
  ;; construct clojure code which will construct the given R-expr
  (cond (rexpr? r)
        (let [rname (rexpr-name r)]
          `(~(ns-resolve (find-ns 'dyna.rexpr-constructors) (symbol (str "make-" rname)))
            ~@(doall (map make-cljcode-to-make-rexpr (get-arguments r)))))

        (is-constant? r)
        `(make-constant (quote ~(get-value r)))

        (instance? jit-local-variable-rexpr r)
        `(make-constant ~(.local-var-symbol ^jit-local-variable-rexpr r))

        (is-variable? r)
        (let [vinfo (*jit-get-variable* r)]
          (if (:local-variable-value vinfo)
            `(make-constant (quote ~(:local-variable-value vinfo)))
            (do (assert (:local-variable vinfo))
                (:local-variable vinfo))))

        :else
        (do (debug-repl "todo handle")
            (???))
        ))

(declare simplify-jit)
(def ^:dynamic *generate-namespace*)
(def ^:dynamic *local-symbols* {}) ;; local symbols and what they resolve to

(declare transform-cljcode-to-jit)

(defn- get-value-cljcode [variable]
  (let [val (*local-symbols* variable)]
    (if (is-constant? (:value val))
      `(quote ~(get-value (:value val))) ;; constant can get directly embedded, use quote in case this is a symbol or something that could possibly get evaled
      (let [v (*jit-get-variable* (:rexpr-var val))]
        (cond (:local-variable-value v)
              (:local-variable-value v) ;; the value of this is stored in a local variable, so we can just use that

              (:local-variable v)
              `(get-value ~(:local-variable v)) ;; this is a variable which contains the matched expression, so we have to use get-value
              :else (do (debug-repl "???")
                        (???)) ;; TODO: handle this somehow?
              )))))

(alter-meta! #'get-value assoc :dyna-jit-inline (fn [form]
                                                  (get-value-cljcode (second form))))

(alter-meta! #'let assoc :dyna-jit-inline (fn [form]
                                            (let [assignments (cdar form)]
                                              ((fn rec [args]
                                                 (if (empty? args) `(do ~@(doall (map transform-cljcode-to-jit (cddr form))))
                                                     (let [[k v & other] args
                                                           compute-code (transform-cljcode-to-jit v)]
                                                       `(let [~k ~compute-code]
                                                          ~(binding [*local-symbols* (assoc *local-symbols* k {:local-var true
                                                                                                               :compute-code compute-code})]
                                                             (rec other))))))
                                               assignments))))

(defn- transform-symbol [symbol]
  (let [r (ns-resolve *generate-namespace* symbol)
        default (fn [body] `(~symbol ~@(doall (map transform-cljcode-to-jit body))))]
    (if (nil? r)
      default
      (:dyna-jit-inline (meta r) default))))

(defn- transform-symbol-function [s]
  (if (contains? *local-symbols* s)
    (fn [form] (reverse (into () (map transform-cljcode-to-jit form))))
    (let [rs (ns-resolve *generate-namespace* s)
          inline-func (:dyna-jit-inline (meta rs))]
      (if-not (nil? inline-func)
        inline-func
        (if (nil? rs)
          (fn [form] (reverse (into () (map transform-cljcode-to-jit form))))
          (fn [form] `(~rs ~@(doall (map transform-cljcode-to-jit (rest form))))) ;; use the ns-resolved version of the symbol
          )))))

(defn- transform-cljcode-to-jit [form]
  (cond (and (symbol? form) (contains? *local-symbols* form)) form
        (and (symbol? form) (ns-resolve *generate-namespace* form)) (ns-resolve *generate-namespace* form)
        (vector? form) (into [] (map transform-cljcode-to-jit form))
        (map? form) (into {} (for [[k v] form] [(transform-cljcode-to-jit k) (transform-cljcode-to-jit v)]))
        (set? form) (into #{} (map transform-cljcode-to-jit form))
        (and (seq? form) (symbol? (first form))) (let [f (first form)]
                                                   (if-not (contains? *local-symbols* f)
                                                     ((transform-symbol-function f) form)
                                                     (reverse (into () (map transform-cljcode-to-jit form)))))
        (seq? form) (reverse (into () (map transform-cljcode-to-jit form)))
        :else (do
                (debug-repl "??? transform form")
                form)))

(defn- simplify-jit-generic [rexpr simplify-method]
  ;; this is called when there is no rewrite for a specific type already defined
  ;; this is going to have to look through the possible rewrites which are defined for a given type
  (let [simplify-mode (:simplify-mode *jit-current-compilation-unit*)
        rewrites (get @rexpr-rewrites-source (type rexpr) [])
       ; matching-rewrites (sort-by compute-rewrite-ranking > (into [] (filter #(check-matches rexpr (:matcher %)) rewrites)))
        matching-rewrites (sort-by compute-rewrite-ranking > (into [] (remove nil? (map (fn [rr]
                                                                                          (let [[suc matching] (compute-match rexpr (:matcher rr))]
                                                                                            (when suc
                                                                                              (assoc rr :matching-vars matching))))
                                                                                        rewrites))))
        ret
        (if (empty? matching-rewrites)
          rexpr ;; then no rewrwite apply to this expression, so we are just going to leave it as is
          (let [picked-rewrite (first matching-rewrites)
                kw-args (:kw-args picked-rewrite)]
            (binding [*generate-namespace* (strict-get picked-rewrite :namespace)]
              (cond ;; this should match dyna.rexpr/make-rewrite-func-body
                (:check kw-args false)
                (let []
                  (debug-repl "check rewrite")
                  (???))

                (:assigns-variable kw-args false)
                (let [assigned-variable (:assigns-variable kw-args)
                      var-mapping (strict-get picked-rewrite :matching-vars)
                      saved-in-local (gensym 'compute-result)]
                  (binding [*local-symbols* (merge *local-symbols*
                                                   var-mapping)]
                    (let [compute-value-code (transform-cljcode-to-jit (:rewrite-body picked-rewrite))
                          assign-value-code (generate-cljcode-assign-value
                                             (strict-get (strict-get var-mapping assigned-variable) :rexpr-var)
                                             saved-in-local)]
                      (add-to-generation! (fn [body]
                                            ;; this needs to track that the variable is now assigned.  If something will have that it can
                                            `(let [~saved-in-local ~compute-value-code]
                                               ~assign-value-code
                                               ~(body))))
                                        ;(debug-repl "ww" false)
                      (make-multiplicity 1))
                    ))

                (:assigns kw-args false)
                (let []
                  (debug-repl "assigns many")
                  (???))

                (:infers kw-args false)
                (let []
                  ;; not sure if want this in the JITted code?  It would have to
                  ;; check the context of the outer constraints, though I suppose
                  ;; that we could just make the context be the constraints which
                  ;; are inside of the JITted block?
                  (debug-repl "infers new rexprs")
                  (???))

                #_(let [var-mapping (strict-get picked-rewrite :matching-vars)
                        assign-expr (strict-get kw-args :assignment-computes-expression)
                        assign-var (strict-get kw-args :assignment-computes-var)
                        assign-inputs (strict-get kw-args :assignment-requires-ground-vars)
                        zzz (debug-repl)
                        inputs-let-bindings (into [] (concat (for [v assign-inputs]
                                                               [v (get-value-cljcode (strict-get (get var-mapping v) :rexpr-var))])))
                        ]
                    (debug-repl "assign rewrite")
                    (???))

                :else
                (do
                  (debug-repl "other rewrite")
                  (???))
                ))
            ))]
    ;(debug-repl "generic simplify")
    ret))

(defn simplify-jit [rexpr]
  (debug-binding
   [*current-simplify-stack* (conj *current-simplify-stack* rexpr)
    *current-simplify-running* simplify-jit]
   (assert (nil? (rexpr-jit-info rexpr))) ;; otherwise this is an already generated expression
   (let [jit-specific (get @rexpr-rewrites-during-jit-compilation (type rexpr) [])
         jit-res (first (remove nil? (for [f jit-specific]
                                       (f rexpr simplify-jit))))
         ret (if (nil? jit-res)
               (simplify-jit-generic rexpr simplify-jit)
               jit-res)]
     ;(debug-repl)
     ret
     )))

(defn- simplify-jit-top [rexpr]
  (loop [r rexpr]
    (let [ret (simplify-jit r)]
      (if (not= r ret)
        (recur ret)
        ret))))

(defn synthize-rewrite-cljcode [rexpr & vargs]
  ;; I suppose that the R-expr should be the representation of
  (let [jinfo (rexpr-jit-info rexpr)
        kwargs (apply hash-map vargs)
        values (:values kwargs) ;; these are values which we should specalize into the rewrite
        example-values (:example-values kwargs) ;; these are example values for a varible
        matched-variable-names (vec (repeatedly (count (:variable-order jinfo)) #(gensym 'mv)))
        arg-matchers (merge (:arg-matches kwargs)
                            (into {} (for [[var val] (merge example-values values)]
                                       ;; figure out what matching rules can be used for this value
                                       [var
                                        (get-matchers-for-value val)
                                        ;(into [] (map first (filter (fn [[name func]] (func val)) @rexpr-matchers)))
                                        ]))
                            ) ;; these are modes on the variables which can be matched
        arg-local-variable-map (into {} (for [[k v] (:variable-name-mapping jinfo)]
                                          [k (nth matched-variable-names ((zipmap (:variable-order jinfo) (range)) v))]))
        generate-new-result-state (:jit-result-state kwargs true) ;; the result state should also be a jitted R-expr unless it is a single R-expr expression
        compilation-unit {:simplify-mode :fast ;; will have the inference mode also run once it runs out of fast stuff???
                          } ;; TODO
        primitive-rexpr (:prim-rexpr jinfo)
        rexpr-args-set (into #{} (get-arguments rexpr))
        generate-functions (transient [])
        computed-variable-values (transient {})
        ]
    ;(debug-repl)
    (assert (not (some #(or (rexpr? %) (instance? RexprValue %)) (vals values))))
    (assert (not (some #(or (rexpr? %) (instance? RexprValue %)) (vals example-values))))
    ;; the jit info should contain information about what the origional expression was that this was constructed from
    (assert (not (nil? jinfo)))
    (binding [*jit-current-compilation-unit* compilation-unit
              *jit-get-variable* (fn [var]
                                   (if-not (contains? rexpr-args-set var)
                                     {:not-found true}
                                     (let [val (get values var)
                                           matchers (if (contains? computed-variable-values var)
                                                      @ground-variable-matchers
                                                      (get arg-matchers var []))]
                                       (merge {:var-modes matchers
                                               :local-variable-value (get computed-variable-values var) ;; the variable which contains the raw value (do not use get-value)
                                               :local-variable (get arg-local-variable-map var)  ;; the variable which contains the matched variable expression (needs to use get-value)
                                               :assign-func-cljcode (fn [value-expression]
                                                                      (if (contains? computed-variable-values var)
                                                                        `(if (not= ~(get computed-variable-values var) ~value-expression)
                                                                           (throw (UnificationFailure.)))
                                                                        (do
                                                                          (assert (symbol? value-expression))
                                                                          (assoc! computed-variable-values var value-expression)
                                                                          nil)))}
                                              (when-not (nil? val) {:value val})))))
              *jit-generate-functions* generate-functions]
      (let [ret (simplify-jit-top primitive-rexpr)]
        (when (is-composit-rexpr? ret)
          (debug-repl "ww")
          (???)) ;; TODO: this should get handled with it generating a new JITted R-expr type for this
        ;;(assert (= (make-multiplicity 1) ret)) ;; this is going to need to be converted into something which can
        (when (not= (make-multiplicity 1) ret)
          (debug-repl "bb"))
        (if (= ret primitive-rexpr)
          (do (debug-repl "unable to do anything given the provided modes")
              (???)
              nil)
          (let [construct-rexpr-code (make-cljcode-to-make-rexpr ret)
                variable-values (persistent! computed-variable-values)
                inner-code `(do
                              ;; first we are going to assign to variables anything which has been computed
                              ~@(for [[varname local-var] variable-values]
                                  `(set-value! ~(arg-local-variable-map varname) ~local-var))
                              ;; this will generate the R-expr which is the result from this expression.

                              ;; for now just be simple as this will have to figure out if this should make a new jit expression or if it can just return something directly
                              ;(make-multiplicity 1)
                              ~construct-rexpr-code)
                gf (persistent! generate-functions)
                rewrite-code ((generate-cljcode gf) inner-code)
                full-rewrite `(def-rewrite
                                :jit-compiler-rewrite true ;; indicate that this was generated
                                :run-in-jit false  ;; we do not want to jit code that was already jitted
                                :match {:rexpr (~(:generated-name jinfo)
                                                ~@(let [local-map (into {} (for [[k v] arg-local-variable-map] [v k]))]
                                                    (for [match-name matched-variable-names
                                                          :let [matcher (get arg-matchers (local-map match-name) [])]]
                                                      (if (empty? matcher)
                                                        match-name
                                                        (do (assert (< (count matcher) 2))
                                                            `(~(first matcher) ~match-name)))))
                                                )}
                                ~rewrite-code)
                ]
            (debug-repl "rrs")
            full-rewrite))))))

(defn synthize-rewrite-rule [rexpr & vargs]
  ;; Given that there are lots of expressions which are combined together, this
  ;; could find that there are multiple modes which could be constructed as a
  ;; result.  If something would find that there is osme expression which would
  (let [signature [rexpr vargs]]
    (when-not (contains? @rexpr-rewrites-constructed signature)
      (swap! rexpr-rewrites-constructed conj signature) ;; record that we are going to construct this rewrite
      (let [rewrite-code (apply synthize-rewrite-cljcode rexpr vargs)]
        (when rewrite-code
          (eval `(do (ns dyna.rexpr-jit)
                     ~rewrite-code)))))))


(def-rewrite
  :match (proj (:any A) (:rexpr R))
  :run-at :jit-compiler
  (let [prev-get *jit-get-variable*
        assigned (volatile! nil)]
    (binding [*jit-get-variable* (fn [var]
                                   (if (= var A)
                                     ;; TODO: more matchers which can allow for it to be a a free variable
                                     {:var-modes (if (nil? @assigned)
                                                   @free-variable-matchers
                                                   @ground-variable-matchers)
                                      :local-variable-value @assigned
                                      :assign-func-cljcode (fn [value-expression]
                                                             (if (nil? @assigned)
                                                               (do (assert (symbol? value-expression))
                                                                   (vreset! assigned value-expression)
                                                                   nil)
                                                               `(if (not= ~@assigned ~value-expression)
                                                                  (throw (UnificationFailure.)))
                                                               ))}
                                     (prev-get var)))]
      (let [ret (simplify R)]
        (if-not (nil? @assigned)
          (let [nr (remap-variables ret {A (jit-local-variable-rexpr. @assigned)})]
            ;(debug-repl "projqq")
            nr)
          (make-proj A ret))
        #_(if (and (not (nil? @assigned)) (not (is-multiplicity? ret)))
          (let [nr ]
            ;; the nr rexpr will have the variables replaced with a reference to
            ;; which local variable contains the value.  This is going to have
            ;; to get removed before the R-expr is returned
            (debug-repl "projqq") ;; TODO: this needs to perform renaming of the variables such that it will reference the local variable name
            nr)
          ret)))))
