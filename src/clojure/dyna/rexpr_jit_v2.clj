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
  (:require [clojure.walk :refer [macroexpand-all]])
  (:require [clojure.set :refer [union]])
  (:import [dyna.rexpr proj-rexpr simple-function-call-rexpr conjunct-rexpr disjunct-rexpr])
  (:import [dyna.rexpr_aggregators_optimized aggregator-op-outer-rexpr aggregator-op-inner-rexpr])
  (:import [dyna.rexpr_aggregators Aggregator])
  (:import [dyna RexprValue RexprValueVariable Rexpr DynaJITRuntimeCheckFailed StatusCounters UnificationFailure])
  (:import [dyna ContextHandle ThreadVar RContext]))

;; this is going to want to cache the R-expr when there are no arguments which are "variables"
;; so something like multiplicy can be just a constant value


;; map from the name of the jitted rexpr -> to the metadata which was used during construction
(def rexprs-types-constructed (atom {}))

(def rexpr-rewrites-constructed (atom #{}))

;; a map from an R-expr to a jitted rexpr
(def rexprs-map-to-jit (atom {}))

(def rexpr-convert-to-jit-functions (atom {}))

(declare is-bound-jit?)

(defrecord jit-local-variable-rexpr [local-var-symbol]
  ;; These variables are not exposed externally.  These variables are projected
  ;; out before they reach the top.  We are going to give these variables a name
  ;; when we synthize the R-expr such that we will be able to track them in the
  ;; context of the program
  RexprValueVariable
  (get-value [this] (???))
  (get-value-in-context [this ctx] (???))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] (is-bound-jit? this))
  (is-bound-in-context? [this ctx] (???))
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    (???))
  Object
  (toString [this] (str "(jit-local-variable " local-var-symbol ")")))

(defrecord jit-expression-variable-rexpr [cljcode]
  RexprValueVariable
  (get-value [this] (???))
  (get-value-in-context [this ctx] (???))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] true)
  (is-bound-in-context? [this ctx] true)
  (all-variables [this] #{})
  (get-representation-in-context [this ctx]
    (???))
  Object
  (toString [this] (str "(jit-expression-variable " cljcode ")")))


(defmethod print-method jit-local-variable-rexpr [^jit-local-variable-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))

(defrecord jit-exposed-variable-rexpr [exposed-name]
  ;; For variables which are exposed on the current synthized R-expr.  These
  ;; variables can be access by doing `(. rexpr ~exposed-name) to read a field
  ;; off of the R-expr
  RexprValueVariable
  (get-value [this] (???))
  (get-value-in-context [this ctx] (???))
  (set-value! [this value] (???))
  (set-value-in-context! [this ctx value] (???))
  (is-bound? [this] (???))
  (is-bound-in-context? [this ctx] (???))
  (all-variables [this] #{this})
  (get-representation-in-context [this ctx]
    this)
  Object
  (toString [this] (str "(jit-exposed-variable-rexpr " exposed-name ")")))


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

(defmethod print-method jit-exposed-variable-rexpr [^jit-exposed-variable-rexpr this ^java.io.Writer w]
  (.write w (.toString this)))

#_(defrecord jit-placeholder-variable-rexpr [^RexprValueVariable wrapped]
  RexprValueVariable
  (get-value [this] (get-value wrapped))
  (get-value-in-context [this ctx] (get-value-in-context wrapped ctx))
  (set-value! [this value] (set-value! wrapped value))
  (set-value-in-context! [this ctx value] (set-value-in-context! wrapped ctx value))
  (is-bound? [this] (is-bound? wrapped))
  (is-bound-in-context? [thix ctx] (is-bound-in-context? wrapped ctx))
  (all-variables [this] #{wrapped})
  (get-representation-in-context [this ctx] (get-representation-in-context wrapped ctx))
  Object
  (toString [this] (str "(jit-placeholder-variable-rexpr " wrapped ")")))

;; the iterables should be something like which variables and their orders can be
(def-base-rexpr jit-placeholder [:unchecked external-name ;; non-nil if accessed via the passed in rexpr
                                 :unchecked local-name ;; if partially rewritten, and now held in a local variable, then non-nil
                                 :var-list placeholder-vars
                                 ]
  #_(exposed-variables [this]
                       (set (map ->jit-placeholder-variable-rexpr (filter is-variable? (vals placeholder-vars))))))

(defn- convert-to-primitive-rexpr [rexpr]
  ;; Not 100% sure if this method is really needed anymore, it seems like is essentially doing nothing
  (cond
    (is-jit-placeholder? rexpr) rexpr  ;; this is already a placeholder, so this just gets returned
    (is-disjunct? rexpr) (let [;evars (exposed-variables rexpr)
                               ]
                           ;; this is already a primitive, so we can just continue to
                           ;(debug-repl "prim disjunct")
                           (rewrite-rexpr-children-no-simp rexpr convert-to-primitive-rexpr))
    (or (is-disjunct-op? rexpr) (is-user-call? rexpr))
    (let []
      (debug-repl "bad rexpr")
      (throw (IllegalArgumentException. (str "Can not covert " (rexpr-name rexpr) " to primitive for JIT, should have been a hole"))))

    :else (rewrite-rexpr-children-no-simp (primitive-rexpr rexpr) convert-to-primitive-rexpr)))

(defn- get-placeholder-rexprs [rexpr]
  (for [c (get-children rexpr)
        z (if (is-jit-placeholder? c) [c] (get-placeholder-rexprs c))]
    z))

(defn- get-variables-and-path [rexpr]
  (cond (is-proj? rexpr) (let [body-path (get-variables-and-path (:body rexpr))
                               var (:var rexpr)
                               child-uses (some #(contains? (exposed-variables %) var)
                                                (filter is-jit-placeholder? (vals body-path)))]
                           (merge (into {} (for [[path v] body-path]
                                             (if (not= v var)
                                               [(cons :body path) v])))
                                  (if child-uses
                                    {(list :var) {:hidden-var var}})))
        (is-aggregator? rexpr) (???)
        (is-aggregator-op-inner? rexpr) (let [body-path (get-variables-and-path (:body rexpr))
                                              proj-out (:projected rexpr)
                                              child-uses (apply union (map exposed-variables (filter is-jit-placeholder? (vals body-path))))]
                                          (when-not (empty? proj-out)
                                            (debug-repl "agg inner vpath for proj")
                                            (???))
                                          (merge (into {} (for [[path v] body-path]
                                                            [(cons :body path) v]))
                                                 (when (contains? child-uses (:incoming rexpr))
                                                   {(list :incoming) {:hidden-var (:incoming rexpr)}})))
        (is-jit-placeholder? rexpr) (merge
                                     {() rexpr}
                                     (into {} (for [[i v] (zipseq (range) (:placeholder-vars rexpr))]
                                                [(list :placeholder-vars `(nth ~i)) v])))

        :else
        (let [litems (rexpr-map-function-with-access-path rexpr
                                                          (fn fr [fname ftype val]
                                                            (case ftype
                                                              :rexpr (if false;(is-jit-placeholder? val)
                                                                       [[(list fname) val]] ;; this is a base case, so we stop
                                                                       ;; then we are going to keep going
                                                                       (for [[path v] (get-variables-and-path val)]
                                                                         [(cons fname path) v]))
                                                              :rexpr-list (for [[i r] (zipseq (range) val)
                                                                                [rp rr] (fr `(nth ~i) :rexpr r)]
                                                                            [(cons fname rp) rr])
                                                              :var [[(list fname) val]]
                                                              :value [[(list fname) val]]
                                                              :var-list (for [[i v] (zipseq (range) val)]
                                                                          [(list fname `(nth ~i)) v])
                                                              :var-map (???) ;; this is going to have to use the key for the access path...
                                                              :hidden-var [[(list fname) {:hidden-var val}]] ;; unsure what do do with this....???
                                                              :unchecked [] ;; there are no "vars" in this
                                                              :file-name []
                                                              :str []
                                                              :mult []
                                                              (do
                                                                (debug-repl "unsure type required mapping")
                                                                (???)))))]
          (into {} (apply concat (vals litems))))))

#_(defn- get-variables-values-letexpr [root-var vars-path]
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

(defn- primitive-rexpr-cljcode
  ([varmap rexpr]
   (primitive-rexpr-cljcode varmap rexpr :rexpr))
  ([varmap rexpr typ]
   (cond (rexpr? rexpr)
         (cond (is-proj? rexpr) (let [new-var (gensym 'projvar)]
                                  `(let [~new-var (make-variable (Object.))]
                                     (make-no-simp-proj ~new-var ~(primitive-rexpr-cljcode (assoc varmap (:var rexpr) new-var) (:body rexpr)))))
               (is-aggregator-op-inner? rexpr) (let [new-incoming (gensym 'aggin)
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
                                                 ret)

               (is-jit-placeholder? rexpr) (let []
                                             (assert (:external-name rexpr)) ;; the primitive-rexpr code is only call on the instance of the R-expr
                                             ;; so we can just return its value directly
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
                                               vs (cons incoming proj-out)]
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
                               ret (make-no-simp-aggregator-op-inner (:operator v) (get new-args incoming incoming) (vec (map #(get new-args % %) proj-out)) body)
                               ]
                           ret)

                         (is-jit-placeholder? v)
                         (let []
                           v ;; this will just keep the placeholder expression in the resulting R-expr
                           )

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

(defn- generate-conversion-function-matcher [matching-against-var
                                             matching-value
                                             values-to-vars
                                             inner-function]
  (cond
    (or (is-conjunct? matching-value)
        (is-disjunct? matching-value))
    (let [argv (gensym 'argv)]
      `(when (~(if (is-conjunct? matching-value) 'is-conjunct? 'is-disjunct?) ~matching-against-var)
         (let [~argv (:args ~matching-against-var)]
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
    `(when (= (get-value ~matching-against-var) ~(get-value matching-value))
       ~(inner-function values-to-vars))

    (is-variable? matching-value)
    (if (contains? values-to-vars matching-value)
      `(when (= ~(strict-get values-to-vars matching-value) ~matching-against-var) ;; I suppose that this could consider the current value
         ~(inner-function values-to-vars))
      (inner-function (assoc values-to-vars
                             matching-value matching-against-var)))

    (instance? Aggregator matching-value)
    `(when (= (. ~(with-meta matching-against-var{:tag Aggregator}) ~'name) ~(.name ^Aggregator matching-value))
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
                        (generate-conversion-function-matcher (:var f)
                                                              (:cur-value f)
                                                              values-to-vars
                                                              #(br r %)))))]
      `(when (~(symbol "dyna.rexpr-constructors" (str "is-" (rexpr-name matching-value) "?")) ~matching-against-var)
         (let [~@(apply concat (map :let-expr var-expands))]
           ~(body-fn var-expands values-to-vars))))

    :else
    (do
      (debug-repl "no match")
      (???))))


(defn- synthize-rexpr-cljcode [rexpr]
  ;; this should just generate the required clojure code to convert the rexpr
  ;; (argument) into a single synthic R-expr.  This is not going to evaluate the code and do the conversion

  (let [prim-rexpr (convert-to-primitive-rexpr rexpr)
        exposed-vars (set (filter is-variable? (exposed-variables rexpr)))
        placeholder-rexprs (set (get-placeholder-rexprs rexpr))
        root-rexpr (gensym 'root) ;; the variable which will be the argument for the conversions
        vars-path (get-variables-and-path rexpr)
        ;[var-access var-gen-code] (get-variables-values-letexpr root-rexpr (keys vars-path)) ;; this might have to handle exceptions which are going to thrown by the
        new-rexpr-name (gensym 'jit-rexpr)
        new-arg-names (merge (into {} (map (fn [v] [v (gensym 'jv)]) exposed-vars))
                             (into {} (map (fn [r] [r (:external-name r)]) placeholder-rexprs)))
        new-arg-names-rev (into {} (for [[k v] new-arg-names]
                                     [v k]))
        new-arg-order (vec (vals new-arg-names))
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
                               ~(primitive-rexpr-cljcode new-arg-names prim-rexpr)))
                            (defmethod rexpr-printer ~(symbol (str new-rexpr-name "-rexpr")) ~'[r]
                              (rexpr-printer (primitive-rexpr ~'r))))
        ;zzz (debug-repl "zzz")
        conversion-function-expr `(fn [~root-rexpr]
                                    (first
                                     ~(generate-conversion-function-matcher root-rexpr
                                                                            prim-rexpr
                                                                            {}
                                                                            (fn [values-to-vars]
                                                                              `(list ;; return a list, as we are getting the first element from the iterator
                                                                                (~(symbol (str "make-" new-rexpr-name))
                                                                                 ~@(for [a new-arg-order]
                                                                                     (strict-get values-to-vars
                                                                                                 (strict-get new-arg-names-rev a)))))))))
        ;zzz2 (debug-repl "zzz2" false)
        ;; conversion-function-expr-old `(fn [~root-rexpr]
        ;;                             (let ~var-gen-code ;; this is going to get access to all of the
        ;;                               ;; this will check that we have all of the arguments (non-nil) and that the constant values are the same as what we expect
        ;;                               #_(when (and
        ;;                                      ;; check that all of the constants embedded in the R-expr are the same
        ;;                                      ~@(for [[vpath val] vars-path
        ;;                                              :when (is-constant? val)]
        ;;                                          `(= (get-value ~(strict-get var-access vpath)) ~(get-value val)))
        ;;                                      ;; check that the R-expr structure is the same
        ;;                                      ~@(for [[vpath val] vars-path
        ;;                                              :when (rexpr? val)]
        ;;                                          `(~(symbol "dyna.rexpr-constructors" (str "is-" (rexpr-name val) "?"))
        ;;                                            ~(strict-get var-access vpath))
        ;;                                          )
        ;;                                      ~@(for [[vpath val] vars-path]
        ;;                                          )))

        ;;                               (when (and ~@(for [[vpath val] vars-path]
        ;;                                              (cond (is-constant? val) `(= ~(strict-get var-access vpath) ~val)
        ;;                                                    (is-variable? val) `(not (nil? ~(strict-get var-access vpath)))
        ;;                                                    (rexpr? val) `(rexpr? ~(strict-get var-access vpath))
        ;;                                                    :else (do (debug-repl "zz")
        ;;                                                              (???)))))
        ;;                                 (~(symbol (str "make-" new-rexpr-name))
        ;;                                  ~@(for [a new-arg-order]
        ;;                                      (strict-get var-access
        ;;                                                  (strict-get (into {} (for [[k v] vars-path] [v k]))
        ;;                                                              (get new-arg-names-rev a))))))))
        ;; zzz (debug-repl "zzz")

        ret {:orig-rexpr rexpr
             :prim-rexpr prim-rexpr
             :generated-name new-rexpr-name
             :make-rexpr-type rexpr-def-expr
             :conversion-function-expr conversion-function-expr
             :variable-name-mapping new-arg-names ;; map from existing-name -> new jit-name
             :variable-order new-arg-order ;; the order of jit-names as saved in the R-expr
             :prim-rexpr-placeholders (primitive-rexpr-with-placeholders prim-rexpr new-arg-names)
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
                       (do (binding [*ns* dummy-namespace]
                             (try
                               (eval `(do
                                        (ns dyna.rexpr-jit-v2)
                                        ~(:make-rexpr-type rtype)))
                               (catch RuntimeException err
                                 (do
                                   (println "failed generate code")
                                   (aprint (:make-rexpr-type rtype))
                                   (throw err)))))
                           (let [f (binding [*ns* dummy-namespace]
                                     (eval `(do
                                              (ns dyna.rexpr-jit-v2)
                                              ~(:conversion-function-expr rtype))))]
                             (swap! rexpr-convert-to-jit-functions assoc rexpr f)
                             f))
                       (get @rexpr-convert-to-jit-functions rexpr))]
      ;; return the converted rexpr as well as the type information for this expression
      [(convert-fn rexpr) rtype])))



(defn- convert-to-jitted-rexpr-fn [rexpr]
  ;; there are some R-expr types which we do not want to JIT, so those are going to be things that we want to replace with a placeholder in the expression
  (if-not (tlocal system/generate-new-jit-states)
    rexpr ;; I suppose that we can just return the R-expr unmodified in the case that there is nothing that we are going to do here
    (let [pl (volatile! {})
          rp (fn rr [rexpr]
               (let [jinfo (rexpr-jit-info rexpr)]
                 (if-not (:jittable jinfo true)
                   (cond
                     (is-aggregator? rexpr) (rr (convert-basic-aggregator-to-op-aggregator rexpr))

                     (is-disjunct-op? rexpr) (let [trie (:rexprs rexpr)
                                                   vars (:disjunction-variables rexpr)
                                                   elems (take 11 (trie/trie-get-values trie nil))
                                                   all-ground (every? (fn [z] (every? #(not (nil? %)) z)) (map first elems))]
                                               (if (or (> (count elems) 8) all-ground)
                                                 (let [id (gensym 'jr)
                                                       exposed (exposed-variables rexpr)]
                                                   ;; then there are 8 or more disjuncts contained in the trie, so we are not going to compile this
                                                   ;; and instead leave it as a hash table

                                                   ;; this is going to need to figure out which variables it cares about inside of the placeholder.  The placeholder
                                                   ;; variables that it identifies will matter, so if it changes it to the "order" of the variables,
                                                   ;; then those are going to have to handle the different expressions which are present
                                                   ;; though if the variables are not present in the other parts of the expression

                                                   ;; I suppose that it could also have that those other variables are going to figure out which

                                                   ;; I suppose that disjunct and aggregators need to know which variables they are over.
                                                   ;; but if the variable does not contain the right expression
                                                   ;; I suppose that the order in which variables appear in the jit-hole would possibly allow for different expressions
                                                   ;; the issue would mostly be around if the conversion happens twice, and the two states become aliased incorrectly.
                                                   ;; How those states would become aliased, it might identify that some of the states will

                                                   (vswap! pl assoc id rexpr)
                                                   (make-jit-placeholder id nil (vec exposed)))
                                                 (let [;; there are 8 or less elements in the trie, so we are going to convert it to a the basic disjunct
                                                       ;; and then add that into the compilation
                                                       new-disjuncts (vec (for [[vals rx] elems
                                                                                :let [vals-r (vec (for [[val var] (zipseq vals vars)
                                                                                                        :when (not (nil? val))]
                                                                                                    (make-no-simp-unify var (make-constant val))))]]
                                                                            (make-conjunct (conj vals-r (rr rx)))))
                                                       ret (make-no-simp-disjunct new-disjuncts)]
                                                   ret)))

                     :else
                     (let [id (gensym 'jr)
                           exposed (exposed-variables rexpr)]
                       ;; should the nested expressions also become JITted?  In the
                       ;; case of an aggregator, we might want to pass through the
                       ;; aggregation to handle its children?  Though those will be
                       ;; their own independent compilation units
                       (vswap! pl assoc id rexpr)
                       (make-jit-placeholder id nil (vec exposed))))
                   (rewrite-rexpr-children-no-simp rexpr rr))))
          nr (rp rexpr)
          [synthed _] (synthize-rexpr nr)]
      (if-not (empty? @pl)
        (let [synthed-holes
              (into {}
                    (for [[key rr] @pl
                          :when (is-disjunct-op? rr)]
                      ;; this is going to attempt to jit all of the bodies of the disjunct.  I suppose that this should have some threshold for if this is going
                      ;; to be useful?  Or if this should figure out if there is going to be some other expression
                      [key
                       (if (is-disjunct-op? rr)
                         (rewrite-rexpr-children rr convert-to-jitted-rexpr-fn)
                         rr)]))
              ret (rewrite-rexpr-children synthed
                                          (fn [r]
                                            (if (is-jit-placeholder? r)
                                              (strict-get synthed-holes (:external-name r))
                                              r)))]
          ;(debug-repl "handle holes")
          ret)
        synthed))))

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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro ^:private bad-gen [& args] (throw (RuntimeException. "BAD code generation.  Attempted to use some code in the generated output which should have never been used")))

(def ^{:private true :dynamic true} *jit-generating-rewrite-for-rexpr* nil
  ;; set to the root R-expr which we are creating a rewrite for
  )
(def ^{:private true :dynamic true} *jit-generating-in-context* nil
  ;; set to the context which the root R-expr is present in
  )

(def ^{:private true :dynamic true} *current-assignment-to-exposed-vars* {}
  ;; variables which are exposed will have some current value.  These values can be looked up using the *jit-generating-in-context*
  ;; with this indirecting through what needs to happen for a given value
  )

(def ^{:private true :dynamic true} *local-variable-names-for-variable-values* nil;(volatile! nil)
  ;; values from variables which have been read can be stored in a local variable.  these variables can just read from these local variables instead of looking through the context
  ;; if a variable value's is read, then it should get saved to a local variable somewhere
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
(def ^{:private true :dynamic true} *jit-call-simplify-on-placeholders* false
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

(defn jit-metadata []
  (let [r (get @*jit-rexpr-rewrite-metadata* *jit-currently-rewriting*)]
    (if (nil? r)
      (get (vswap! *jit-rexpr-rewrite-metadata* assoc *jit-currently-rewriting* (volatile! {})) *jit-currently-rewriting*)
      r)))

(defn- generate-cljcode [generate-functions]
  (if (empty? generate-functions)
    (fn [f] (f))
    (let [f (first generate-functions)
          r (generate-cljcode (rest generate-functions))]
      (fn [inner] (f (partial r inner))))))

(defn can-generate-code? []
  (not (nil? *jit-generate-functions*)))

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

(defn- generate-cljcode-to-materalize-rexpr [rexpr & {:keys [simplify-result] :or {simplify-result false}}]
  ;; this is going to have to figure out which variables are referencing some value
  ;; and then create a new R-expr type with holes, and generate the new "make R-expr"

  ;; if simplify result is true, then we should pass the expression to simplify
  ;; again.  This will allow for checkpoints to keep rewriting from its
  ;; seralized state, whereas for an ending state, we might just want to return
  ;; it, as it should go back into the control flow of "other" stuff
  (if (is-empty-rexpr? rexpr)
    `(throw (UnificationFailure. "JIT multiplicity 0")) ;; faster specical case handling for when it gets a mult 0 meaning that unification has failed
    (let [re (if-not (is-composit-rexpr? rexpr)
               (let [local-vars-bound @*local-variable-names-for-variable-values*]
                 ;; this is a simple primitive R-expr type (like multiplicity or builtin
                 ;; like add) there is no reason to generate a more complex R-expr type for
                 ;; this.  So we are going to just generate something which generates this type directly
                 `(~(symbol "dyna.rexpr-constructors" (str "make-" (rexpr-name rexpr)))
                   ~@(for [arg (get-arguments rexpr)]
                       (cond (number? arg) arg
                             (is-constant? arg) `(make-constant ~(get-value arg))
                             (instance? jit-exposed-variable-rexpr arg)
                             (if (contains? local-vars-bound arg)
                               `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                               `(. ~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))})
                                   ~(:exposed-name arg)))
                             (and (instance? jit-local-variable-rexpr arg) (is-bound-jit? arg))
                             `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                             :else (do (debug-repl "arg type")
                                       (???))))))
               (let [local-vars-bound @*local-variable-names-for-variable-values*
                     exposed (exposed-variables rexpr)
                     remapped-locals (into {} (for [v exposed
                                                    :when (or (instance? jit-local-variable-rexpr v)
                                                              (instance? jit-hidden-variable-rexpr v)
                                                              (instance? jit-exposed-variable-rexpr v))]
                                                [v (make-variable (gensym 'vhold))]))
                     new-r (remap-variables rexpr remapped-locals)
                     [_ new-synth] (synthize-rexpr new-r)
                     rlocal-map (into {} (for [[k v] remapped-locals] [v k]))
                     rvarmap (into {} (for [[k v] (:variable-name-mapping new-synth)] [v k]))]
                 `(~(symbol "dyna.rexpr-constructors" (str "make-" (:generated-name new-synth)))
                   ~@(for [v (:variable-order new-synth)
                           :let [lv (rvarmap v)
                                 arg (get rlocal-map lv lv)]]
                       (cond (instance? jit-exposed-variable-rexpr arg)
                             (if (contains? local-vars-bound arg)
                               `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                               `(. ~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))})
                                   ~(:exposed-name arg)))
                             (and (instance? jit-local-variable-rexpr arg) (is-bound-jit? arg))
                             `(make-constant ~(strict-get (local-vars-bound arg) :var-name))
                             (instance? jit-expression-variable-rexpr arg)
                             `(make-constant ~(:cljcode arg))
                             :else (do (debug-repl "arg type")
                                       (???)))))))]
      (if (and simplify-result (not (is-multiplicity? rexpr)))
        `(~'simplify ~re)
        re))))

(defn- add-return-rexpr-checkpoint! [rexpr]
  (let [materalize-code (generate-cljcode-to-materalize-rexpr rexpr :simplify-result true)
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
  (let [materalize-code (generate-cljcode-to-materalize-rexpr rexpr :simplify-result false)]
    (add-to-generation! (fn [inner]
                          `(try
                             ~(inner)
                             (catch UnificationFailure ~'_
                               ~materalize-code))))))

(defn- generate-cljcode-fn [final-rexpr]
  `(fn [~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))}) ~'simplify]
     ~(when system/status-counters `(StatusCounters/match_attempt))
     (let [^RContext ~'**context** (ContextHandle/get)
           ^ThreadVar ~'**threadvar** (ThreadVar/get)]
       (try
         (do ~((generate-cljcode (persistent! *jit-generate-functions*))
               (fn []
                 (generate-cljcode-to-materalize-rexpr final-rexpr)
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
  `(jit-precondition-to-check ~condition))

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

(defn- concat-code [& args]
  (let [a (remove #(or (nil? %) (boolean? %) (string? %) (number? %)) (drop-last args))
        l (last args)]
    (if (#{:rexpr :rexpr-value :value :rexpr-value-list :rexpr-list} (:type l))
      (assoc l :cljcode-expr `(let* [] ~@a ~(:cljcode-expr l)))
      `(let* [] ~@a ~l))))

(defn- add-precondition-on-same-value! [value]
  (add-to-generation! (gen-precondition-on-same-value value)))

(def ^:private evaluate-symbol-meta (atom {}))  ;; symbols like 'do, are compiler builtins and not variables, so we can't easily associate meta with them

(declare ^{:private true} simplify-jit-internal-rexpr)

(defn- get-current-value [value]
  (case (:type value)
    :value (cond (contains? value :constant-value) (:constant-value value)
                 (contains? value :current-value) (:current-value value)
                 :else nil)
    :rexpr-value (or (:current-value value)
                     (:constant-value value))
    (let []
      (debug-repl "todo: unknown current value type")
      (???))))

(defn- has-current-value? [value]
  (or (contains? value :constant-value) (contains? value :current-value)))

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

          (and (map? expr)
               (#{:rexpr :rexpr-value :value :rexpr-value-list :rexpr-list} (:type expr))) expr ;; this is already something that was evaluated by the JIT, so we are just going to pass it through

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
                                                                 :rexpr-list (let [v (debug-repl "rl")
                                                                                   z (vec (map :rexpr-type (:current-value g)))]

                                                                               z)
                                                                 :rexpr-value-list (do
                                                                                     (debug-repl)
                                                                                     (???))
                                                                 ))]
                                                    ;(debug-repl "make r-expr")
                                                    {:type :rexpr
                                                     :rexpr-type (apply (resolve sn) argg)}))}
                                       {:type :function
                                        :invoke (fn [[sn & args]]
                                                  (jit-evaluate-cljform `(~'simplify-construct (~(symbol "dyna.rexpr-constructors" (str "make-no-simp-" (:rexpr-constructor m)))
                                                                                                ~@args))))})

                                     (and (ifn? (var-get var)) (= (find-ns 'clojure.core) (:ns m)))
                                     {:type :function
                                      :invoke (fn [[func & args]]

                                                (let [avals (vec (map jit-evaluate-cljform args))
                                                      can-eval (every? has-current-value? avals)
                                                      ret {:type :value
                                                           :cljcode-expr `(~(var-get var) ~@(map :cljcode-expr avals))}
                                                      result (when can-eval
                                                               (apply (var-get var) (map get-current-value avals)))]
                                                  (if can-eval
                                                    (assoc ret
                                                           (if (every? #(contains? % :constant-value) avals)
                                                             :constant-value :current-value)
                                                           result)
                                                    ret)))}

                                     :else
                                     (do (debug-repl "symbol ??")
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
                                             :cljcode-expr `(. ~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))})
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

                                            :else (???))

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
                                     :cljcode-expr (vec (map #(:cljcode-expr % `(bad-gen)) vs))}
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
           :invoke (fn [[f & body]]
                     {:type :value
                      :cljcode-expr `(~f ~@(map #(-> jit-evaluate-cljform :cljcode-expr) body))})}

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
                                 cval (get-current-value condv)]
                             (if cval
                               (concat-code
                                (gen-precondition-to-check (:cljcode-expr condv))
                                (jit-evaluate-cljform true-b))
                               (concat-code
                                (gen-precondition-to-check `(not ~(:cljcode-expr condv)))
                                (jit-evaluate-cljform false-b)))))})

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

           :else
           (do
             (dyna-assert (:current-value varj))
             {:type :value
              :cljcode-expr `(is-bound-in-context? ~(:cljcode-expr varj) ~'**context**)
              :current-value (is-bound? (:current-value varj))})))))

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
           {:type :value
            :current-value (is-variable? (get-current-value varj))
            :cljcode-expr `(is-variable? ~(:cljcode-expr varj))}


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
           (let [cval (get-current-value varj)]
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
                :cljcode-expr `(bad-gen)}))

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
     #_(add-to-generation! (fn [inner]
                           `(let* [~local-value-name ~(:cljcode-expr valj)]
                              ~(when (instance? jit-exposed-variable-rexpr (:matched-variable varj))
                                 `(set-value-in-context! ~(:cljcode-expr varj) ~'**context** ~local-value-name))
                              ~(inner))))
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
   (let [valj (jit-evaluate-cljform val)]
     {:type :rexpr-value
      (if (contains? valj :constant-value) :constant-value :current-value) (make-constant (get-current-value valj))
      :cljcode-expr `(make-constant ~(:cljcode-expr valj))})))

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
           types (into #{} (map :type new-vals))]
       (assert (= 1 (count types)))
       {:type (case (first types)
                :rexpr :rexpr-list
                :value :value
                :rexpr-value :rexpr-value-list)
        :current-value (if (= :value (first types))
                         (map :current-value new-vals)
                         new-vals)
        :cljcode-expr `(list ~@(map #(:cljcode-expr % `(bad-gen)) new-vals))}
       ))))

(set-jit-method
 #'vec
 (fn [[_ col]]
   (let [varj (jit-evaluate-cljform col)]
     (case (:type varj)
       :rexpr-list varj  ;; these will just pass through unchecked, as they are giong to end up handled by something else
       :rexpr-value-list varj
       :value (merge {:type :value}
                     (when (contains? :current-value varj)
                       {:current-value (vec (:current-value varj))})
                     :cljcode-expr
                     (let [cc (:cljcode-expr varj)]
                       (if (and (seqable? cc) (not (vector? cc)) (= 'list (first cc)))
                         `[~@(rest cc)] ;; this is like `(list 1 2 3) and change it to be `[1 2 3]
                         `(vec ~cc))))))))

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
             (case m
               and (if (:constant-value f) (jit-evaluate-cljform `(and ~@(rest args))) f)
               or (if (:constant-value f) f (jit-evaluate-cljform `(or ~@(rest args)))))
             (contains? f :current-value)
             (case m
               and (if (:current-value f)
                     (do (gen-precondition-to-check (:cljcode-expr f))
                         (jit-evaluate-cljform `(and ~@(rest args))))
                     (do (gen-precondition-to-check `(not ~(:cljcode-expr f)))
                         f))
               or (if (:current-value f)
                    (do (gen-precondition-to-check (:cljcode-expr f))
                        f)
                    (do (gen-precondition-to-check `(not ~(:cljcode-expr f)))
                        (jit-evaluate-cljform `(or ~@(rest args))))))
             :else (???))))))

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
  [rexpr matcher1]
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
                                  :cljcode-expr `(. ~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))})
                                                    ~(:exposed-name arg))    ;(:exposed-name arg)
                                  :matched-variable arg}

                                 (instance? jit-local-variable-rexpr arg)
                                 (if (contains? @*local-variable-names-for-variable-values* arg)
                                   (let [x (@*local-variable-names-for-variable-values* arg)]
                                     {:type t
                                      :matched-variable arg
                                      :current-value (strict-get x :current-value)
                                      :cljcode-expr `(bad-gen)})
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
                                  :cljcode-expr `(bad-gen)}

                                 (= t :rexpr-value-list)
                                 {:type :rexpr-value-list
                                  :cljcode-expr `(bad-gen) ;; we can not directly generate this representation?  Though the individual variables should still be accessable?
                                  :matched-variable arg
                                  :current-value (vec (for [z arg]
                                                        (cond (instance? jit-exposed-variable-rexpr z)
                                                              {:type :rexpr-value
                                                               :current-value (*current-assignment-to-exposed-vars* (:exposed-name z))
                                                               :cljcode-expr `(. ~(with-meta 'rexpr {:tag (.getName (type *jit-generating-rewrite-for-rexpr*))})
                                                                                 (:exposed-name z))
                                                               :matched-variable z}

                                                              (instance? jit-local-variable-rexpr z)
                                                              (if (contains? @*local-variable-names-for-variable-values* z)
                                                                (let [x (@*local-variable-names-for-variable-values* z)]
                                                                  {:type :rexpr-value
                                                                   :matched-variable z
                                                                   :current-value (strict-get x :current-value)
                                                                   :cljcode-expr `(bad-gen)})
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
                    (vswap! runtime-checks conj (gen-precondition-to-check (:cljcode-expr success)))
                    (list true)))))
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
      (doall (for [_ (match-top matcher rexpr)]
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
              (debug-repl "perform generic rewrite")
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
        (let [jit-specific-rewrites (get @rexpr-rewrites-during-jit-compilation (type rexpr) nil)
              ret (if (nil? jit-specific-rewrites)
                    (simplify-jit-internal-rexpr-generic-rewrites rexpr)
                    (first (remove #(or (nil? %) (= % rexpr))
                                   (for [f jit-specific-rewrites]
                                     (f rexpr simplify-jit-internal-rexpr)))))]
          (if (or (nil? ret) (= ret rexpr))
            rexpr
            (let [m (get @*jit-rexpr-rewrite-metadata* rexpr)]
              ;; track the metadata as the R-expr is changed
              (when-not (nil? m)
                (vswap! *jit-rexpr-rewrite-metadata* assoc ret m))
              ret))))))))



(defn- simplify-jit-internal-rexpr-once [r]
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
        (debug-repl "no possible rewrites" false)
        r) ;; then we are "done" and we just return this R-expr unrewritten
      (loop [picked-rr-order (sort-by (fn [[simplify-stack rr]]
                                        (+ (* 1000 (count simplify-stack)) ;; prefer things at the top of the stack
                                           (if (:aggregator-assign-value false) -20000 0)
                                           (if (contains? (:kw-args rr) :check) -200000 0) ;; checks should go earlier
                                           (if (contains? (:kw-args rr) :assigns-variable) -100000 0) ;; then assignments of variables
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
                                                                 (not= (get pre-local-variable-name-values var) val))
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
             (do (assert (= :rexpr (:type rexpr)))
                 (:rexpr-type rexpr)))]
    (let [nr (simplify-jit-internal-rexpr-once r)]
      (if (not= r nr)
        (recur nr)
        nr))))

#_(defn- simplify-jit-recursive-call [rexpr] )



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
        local-name-to-context (zipmap (:variable-order jinfo) (get-arguments rexpr))]
    ;(debug-repl "aa")
    (binding [*jit-generating-rewrite-for-rexpr* rexpr
              *jit-generating-in-context* context
              *rewrites-allowed-to-run* #{:standard}
              *jit-consider-expanding-placeholders* false ;; TODO: this should eventually be true
              *jit-call-simplify-on-placeholders* false
              *current-assignment-to-exposed-vars* local-name-to-context
              ;*current-simplify-stack* ()
              *local-variable-names-for-variable-values* (volatile! nil)
              *jit-generate-functions* (transient [])
              *jit-incremented-status-counter* (volatile! false)
              *rexpr-checked-already* (transient #{})
              *jit-rexpr-rewrite-metadata* (volatile! {})]
      (tbinding
       [current-simplify-stack ()
        use-optimized-disjunct false]
       (debug-tbinding
        ;; restart these values, as we are running a nested version of simplify for ourselves
        [current-simplify-running nil]
        (let [prim-r (:prim-rexpr-placeholders jinfo)
              result (simplify-jit-internal-rexpr-loop prim-r)]
          (if (not= result prim-r)
            ;; then there is something that we can generate, and we are going to want to run that generation and then evaluate it against the current R-expr
            (let [gen-fn (generate-cljcode-fn result)
                  __ (debug-repl "pr0" false)
                  fn-evaled (binding [*ns* dummy-namespace]
                              (eval `(do
                                       (ns dyna.rexpr-jit-v2)
                                       (def-rewrite-direct ~(:generated-name jinfo) [:standard] ~gen-fn))))]

              (debug-repl "pr1" false)
              (let [rr (try (fn-evaled rexpr simplify-method)
                            (catch UnificationFailure _ (make-multiplicity 0)))]
                (debug-repl "pr2" false)
                (assert (not= rexpr rr)) ;; otherwise there was no rewriting done, and the generated rewrite failed for some reason
                rr))
            (do
              ;; then there was nothing that can be rewritten, so this should just return the same R-expr back
              rexpr))))))))

(defn- maybe-create-rewrites-inference [context rexpr jinfo]
  (???))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def ^{:dynamic true :private true} *has-jit-rexpr-in-expression* (volatile! false))

(defn simplify-jit-create-rewrites-fast [rexpr]
  ;; create rewrites which correspond with simplify-fast
  ;; these rewrites can only look at the bindings to variable values
  ;; just like normal simplify, we are going to have that
  (debug-tbinding
   [current-simplify-stack (conj (tlocal *current-simplify-stack*) rexpr)
    current-simplify-running simplify-jit-create-rewrites-fast]
   (let [ret ((get @rexpr-rewrites-func (type rexpr) simplify-identity) rexpr simplify-jit-create-rewrites-fast)]
     (if (or (nil? ret) (= ret rexpr))
       (let [jinfo (rexpr-jit-info rexpr)]
         (if-not (nil? jinfo)
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
                (if (is-bound-jit? V)
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
  (if (:out-var @*jit-aggregator-info*)
    (:out-var @*jit-aggregator-info*)
    (let [out-var (gensym 'aggoutA)]
      (assert (can-generate-code?))
      (vswap! *jit-aggregator-info* assoc :out-var out-var)
      (add-to-generation! (fn [inner]
                            `(let* [~out-var (volatile! nil)]
                               ~(inner))))
      out-var)))

(def-base-rexpr aggregator-op-partial-result [:var partial-var
                                              :var-list group-vars
                                              :rexpr remains])


(def-rewrite
  :match (aggregator-op-outer (:unchecked operator) (:any result-variable) (:rexpr Rbody1))
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        Rbody2 (if (is-aggregator-op-partial-result? Rbody1)
                   (:remains Rbody1)
                   Rbody1)]
    (vswap! metadata update :outer-call-count (fnil inc 0))
    (vswap! metadata assoc :operator operator)
    (when (nil? (:current-out-var @metadata))
      (vswap! metadata assoc :current-out-var (volatile! nil)))
    (when (and (empty? @metadata) (is-aggregator-op-partial-result? Rbody1))
      (when-not (contains? @metadata :group-vars)
        (vswap! metadata assoc :group-vars (:group-vars Rbody1)))
      (when (and (not (contains? @metadata :out-var))
                 (can-generate-code?))
        (let [out-var (gensym 'aggoutB)
              prev-vals (jit-evaluate-cljform `(get-value ~(:partial-var Rbody1)))]
          (add-to-generation! (fn [inner]
                                `(let* [~out-var (volatile! ~(:cljcode-expr prev-vals))]
                                   ~(inner))))
          (vswap! metadata assoc :out-var out-var))))
    (when-not (contains? @metadata :group-vars)
      (debug-repl)
      (vswap! metadata assoc :group-vars (vec (remove is-bound-jit? (exposed-variables Rbody2)))))

    (if (is-empty-rexpr? Rbody2)
      (do
        (vswap! *jit-simplify-call-counter* inc)
        (vswap! *jit-simplify-rewrites-found* conj [(tlocal *current-simplify-stack*)
                                                    {:runtime-checks []
                                                     :matching-vars []
                                                     :simplify-call-counter @*jit-simplify-call-counter*
                                                     :aggregator-assign-value true
                                                     :kw-args {:agg-final true}}])
        (if (*jit-simplify-rewrites-picked-to-run* {:runtime-checks []
                                                    :matching-vars []
                                                    :simplify-call-counter @*jit-simplify-call-counter*
                                                    :aggregator-assign-value true
                                                    :kw-args {:agg-final true}})
          (if *jit-compute-unification-failure*
            (make-multiplicity 0)
            (let []
              (debug-repl "pick agg")
              (assert (can-generate-code?))
              (assert (empty? (:group-vars @metadata))) ;; TODO
              (if (contains? @metadata :out-var)
                (do
                  (jit-evaluate-cljform `(set-value! ~result-variable ((. ~operator lower-value) (deref ~{:type :value
                                                                                                          :cljcode-expr (:out-var @metadata)}))))
                  (make-multiplicity 1))
                (make-multiplicity 0))
              ))
          nil))
      (let [group-vars (:group-vars @metadata)
            body (binding [*jit-aggregator-info* metadata]
                   (simplify Rbody2))]
        (if (and (= body Rbody2) (nil? (:out-var @metadata)))
          nil ;; then nothing was rewritten
          (do
            (if (and (is-empty-rexpr? body) (empty? (:group-vars @metadata)) (not (contains? @metadata :out-var)))
              (make-multiplicity 0)
              (do
                ;; this is some partially evaluated expression, which will then have to figure out if there is something which could
                ;; allow for it
                                        ;(debug-repl "jit in agg op" false)
                (if-not (contains? @metadata :out-var)
                  (make-no-simp-aggregator-op-outer operator result-variable body)
                  (let [outvar (:out-var @metadata)]
                    (let [ret-body (make-no-simp-aggregator-op-partial-result (jit-expression-variable-rexpr. `(deref ~outvar))
                                                                              group-vars
                                                                              body)
                          ret (make-no-simp-aggregator-op-outer operator
                                                                result-variable
                                                                ret-body)
                          ]
                      (debug-repl "partial agg" false)
                      ret)))))))))))

(def-rewrite
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
                        (get-current-value incoming-val))))  ;; TODO this needs to handle the different values for this
            ;(debug-repl "handle jit agg op inner")
            (make-multiplicity 0) ;; this has already been handled, so we can remove it from the R-expr
            )
          (let [ret (make-no-simp-aggregator-op-inner operator incoming projected-vars body)]
            ;(debug-repl "more to do in aggregator")
            ret))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-rewrite
  :match (disjunct (:rexpr-list children))
  :run-at :jit-compiler
  (let [metadata (jit-metadata)
        ex-child (map exposed-variables children)
        exposed (apply union ex-child)
        handle-disjunct (remove is-bound-jit? exposed) ;; anything that is bound externally does not need to be handled by the disjunct
        ret-children (transient [])
        parent-variable-name-bindings *local-variable-names-for-variable-values*
        changed (volatile! false)
        ]
    (doseq [c children]
      (let [new-binding (volatile! @parent-variable-name-bindings)]
        (let [r (binding [*local-variable-names-for-variable-values* new-binding]
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
            retd (make-disjunct (vec (map first ret)))]
        ;(debug-repl "disjunct match")
        (when-not (empty? handle-disjunct)
          (???))
        ;; this will become a disjunct-op if we use the normal make-disjunct here, and we don't want to have to deal
        ;; when thtat kind of disjunct
        retd))))

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
  :match (jit-placeholder _ _ _)
  :run-at :jit-compiler
  (do
    (debug-repl "jit placeholder internal")
    (???)))


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
