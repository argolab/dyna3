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

;; a map from an R-expr to a jitted rexpr
(def rexprs-map-to-jit (atom {}))

(def rexpr-convert-to-jit-functions (atom {}))


(def ^:dynamic *jit-current-compilation-unit* {})  ;; there needs to be some
                                                   ;; information here which
                                                   ;; represents the current
                                                   ;; compilation unit.

(def ^:dynamic *jit-get-variable*) ;; will be a function that can be called to get information about the flags, mode.

(def ^:dynamic *jit-generate-clojure-code* (volatile! nil))  ;; a volatile which
                                                             ;; is a pointer to
                                                             ;; a function which
                                                             ;; will return the
                                                             ;; generated
                                                             ;; clojure code up
                                                             ;; to this point


(defn delete-rexpr-type [rexpr-name]
  (???) ;; there should be something whic hcould be used to delete an R-expr.
        ;; though if we are deleting the construction functions, then that might
        ;; cause other expressions to break elsewhere.... so not sure how well
        ;; this would work an practice
  )


;; the iterables should be something like which variables and their orders can be
(def-base-rexpr jit-placeholder [:unchecked placeholder-id
                                 :var-list placeholder-vars
                                 :unchecked placeholder-iterables])

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

             ;; ;; should the conversion function have that there is some expression.  In the case that it might result in some of
             ;; ;; if there is something which is giong to construct this value, though there might
             ;; :conversion-function-args (fn [& args] (???))

             ;; ;; check that the shape of the R-expr matches the kind of the thing that we can convert into this generated code
             ;; :check-could-be-converted (fn [rexpr] (???))
             }]


    ;(debug-repl)
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

(defn- check-matches
  ([rexpr matcher already-matched]
   (let [rname (rexpr-name rexpr)
         args (get-arguments rexpr)
         ret (when (= rname (first matcher)) ;; the name on the match expression does not match
               (every? true? (for [[match-expr arg] (zipseq (rest matcher) args)]
                               (cond (= '_ match-expr) true
                                     (symbol? match-expr) (do (assert (not (contains? already-matched match-expr)))
                                                              true)
                                     (and (= 2 (count match-expr))
                                          (not (contains? @rexpr-containers-signature (car match-expr)))
                                          (symbol? (cdar match-expr)))
                                       (let [match-requires (car match-expr)
                                             var-info (cond (is-constant? arg) {:value arg}
                                                            (is-variable? arg) (*jit-get-variable* arg)
                                                            :else (do (debug-repl "todo") (???)))]
                                         (cond (some #{match-requires} (:var-modes var-info [])) true
                                               (and (contains? var-info :value) (contains? @rexpr-matchers match-requires)) ((get @rexpr-matchers match-requires) (:value var-info))
                                               :else (do
                                                       ;(debug-repl "qq")
                                                       false)
                                               ;; TODO: there may be more more cases which can cause something to match
                                               ;; :else (do (debug-repl "todo2")
                                               ;;           (???))
                                               ))
                                       :else (do (debug-repl "todo3")
                                                 (???))))))]

     ;(debug-repl "ww")
     ret))
  ([rexpr matcher] (check-matches rexpr matcher {})))

(defn- compute-rewrite-ranking [rewrite]
  ;; bigger numbers will be perfable rewrites.  Rewrites which directly compute
  ;; a value should be prefered over something which checks for 0 for example.
  (cond (:is-assignment-rewrite (:kw-args rewrite) false) 100
        (:is-check-rewrite (:kw-args rewrite) false) 90
        :else 0))

(defn- is-composit-rexpr [rexpr]
  )

(defn- make-rexpr-type-in-jit [construct-func]
  (fn [& args]
    ;; this will allow us to intercept which functions are called when it is
    ;; doing the construction
    (apply construct-func args)))

(declare simplify-jit)

(defn- simplify-jit-generic [rexpr simplify-method]
  ;; this is called when there is no rewrite for a specific type already defined
  ;; this is going to have to look through the possible rewrites which are defined for a given type
  (let [simplify-mode (:simplify-mode *jit-current-compilation-unit*)
        rewrites (get @rexpr-rewrites-source (type rexpr) [])
        matching-rewrites (sort-by compute-rewrite-ranking > (into [] (filter #(check-matches rexpr (:matcher %)) rewrites)))]
    (debug-repl "generic simplify"))



  (???))

(defn simplify-jit [rexpr]
  (debug-binding
   [*current-simplify-stack* (conj *current-simplify-stack* rexpr)
    *current-simplify-running* simplify-jit]
   (assert (nil? (rexpr-jit-info rexpr))) ;; otherwise this is an already generated expression
   (let [jit-specific (get @rexpr-rewrites-during-jit-compilation (type rexpr) [])
         jit-res (first (remove nil? (for [f jit-specific]
                                       (f rexpr simplify-jit))))
         res (if (nil? jit-res)
               (simplify-jit-generic rexpr simplify-jit)
               jit-res)]
     (debug-repl)
     )
   #_(let [ff (get @rexpr-rewrites-during-jit-compilation-func (type rexpr))
         zz (debug-repl)
         ret ((get @rexpr-rewrites-during-jit-compilation-func (type rexpr) simplify-jit-generic) rexpr simplify-jit)]
     (assert (not (nil? ret)))

     ret)))

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
        arg-matchers (merge (:arg-matches kwargs)
                            (into {} (for [[var val] (merge example-values values)]
                                       ;; figure out what matching rules can be used for this value
                                       [var
                                        (get-matchers-for-value val)
                                        ;(into [] (map first (filter (fn [[name func]] (func val)) @rexpr-matchers)))
                                        ]))
                            ) ;; these are modes on the variables which can be matched
        generate-new-result-state (:jit-result-state kwargs true) ;; the result state should also be a jitted R-expr unless it is a single R-expr expression
        compilation-unit {:simplify-mode :fast ;; will have the inference mode also run once it runs out of fast stuff???
                          } ;; TODO
        primitive-rexpr (:prim-rexpr jinfo)
        rexpr-args-set (into #{} (get-arguments rexpr))
        ]
    ;; the jit info should contain information about what the origional expression was that this was constructed from
    (assert (not (nil? jinfo)))
    (binding [*jit-current-compilation-unit* compilation-unit
              *jit-get-variable* (fn [var]
                                   (assert (contains? rexpr-args-set var)) ;; otherwise this is something that should have been handled?
                                   (let [val (get values var)
                                         matchers (get arg-matchers var [])]
                                     (merge {:var-modes matchers}
                                            (when-not (nil? val) {:value val}))))]
      (let [ret (simplify-jit-top primitive-rexpr)]
        (debug-repl "rrs")

        ;; if this is a complex R-expr, then we might want to make a new R-expr
        ;; type, or find something which corresponds with this R-expr.

        ))))


;; (defn synthize-rexpr-construct-rule [rexpr]
;;   ;;
;;   )

(defn synthize-rewrite-rule [rexpr & vargs]
  ;; Given that there are lots of expressions which are combined together, this
  ;; could find that there are multiple modes which could be constructed as a
  ;; result.  If something would find that there is osme expression which would
  (apply synthize-rewrite-cljcode rexpr vargs)
  )


;; (def-rewrite
;;   :match (proj (:any A) (:rexpr R))
;;   :jit-compiler-rewrite true

;;   )

(def-rewrite
  :match (proj (:any A) (:rexpr R))
  :run-at :jit-compiler
  (let [prev-get *jit-get-variable*]
    (binding [*jit-get-variable* (fn [var]
                                   (if (= var A)
                                     ;; TODO: more matchers which can allow for it to be a a free variable
                                     {:var-modes (get-matchers-for-value (make-variable 'some-free-variable-xxxx))}
                                     (prev-get var)))]
      (simplify R))))
