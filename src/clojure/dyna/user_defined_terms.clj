(ns dyna.user-defined-terms
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.assumptions :refer [invalidate! make-assumption depend-on-assumption]])
  (:require [clojure.set :refer [subset? union]])
  (:import [dyna.rexpr user-call-rexpr]))


;; these are user defs which are always present
;; (def base-user-defs (atom {}))

(defmacro def-user-term [name arity rexpr]
  ;; define a user level term from internal
  (if (not (string? name))
    `(do ~@(for [x name]
             `(def-user-term ~x ~arity ~rexpr)))
    `(swap! system/system-defined-user-term assoc ~[name arity]
            (let [~'self (make-variable "$self")] ;; the self variable can be the current dynabase which is calling this expression, most builtin don't care
              (let ~(vec
                     (mapcat #(list (symbol (str "v" %))
                                    `(make-variable ~(str "$" %)))
                             (range (+ 1 arity))))
                ~rexpr)))))

(defn empty-user-defined-term [name]
  {:def-assumption (make-assumption) ;; the assumption for the definition
   :optimized-assumption (make-assumption) ;; the assumption that there is no more optimized version of this term
   :memoized-assumption (make-assumption) ;; if there is some changed to the memoized value for this term

   ;; if there are macros, then those are going to want to reference the files that they are coming from then I suppoes
   ;; this can check the from_file information on any term which is created I suppose
   ;; if something is a macro, then that means that there are potentially new variables which get introduced?
   ;; but I suppose that can be allowed as long as this just adds in the new project statements
   :is-macro false ;; if this is a macro meaning that this should get called on the AST of some expression, must have that the dynabase not be true

   :dispose-arguments nil ;; if this requires that some of its arguments get quoted.  again require that the program is written such that there aren't already intermediate variables which exist

   :rexprs () ;; R-exprs which have to get merged to gether to represent this term

   :dynabases #{} ;; a set of which dynabases appear on this term.  We might be able to use this to perform some kind of type inference between expressions

   ;; if this is imported from somewhere else, then this is the entire name of that other declared object
   ;; this will then have to recurse in finding the other thing
   :imported-from-another-file nil

   ;; would be nice if there was some kind of return value type information as
   ;; well.  This would have to be something which is cached information I
   ;; suppose that it could look at the various R-exprs which are defined for a
   ;; given term and use that information to identify which expression
   ;; correspond with something

   ;; there should be other fields here which correspond with memoized values or
   :term-name name})


(defn update-user-term [name function]
  (swap! system/user-defined-terms (fn [old]
                                     (let [v (get old name nil)]
                                       (assoc old name (function (if-not (nil? v) v (empty-user-defined-term name))))))))

(defn add-to-user-term [source-file dynabase name arity rexpr]
  (let [object-name (merge {:name name
                            :arity arity}  ;; I suppose that there isn't going to be variable argument expressions, meaning that this will
                           (when (dnil? dynabase) ;; when there is a dynabase, then this requires having to merge across different values
                             {:source-file source-file}))
        value {:source-file source-file
               :dynabase dynabase
               :rexpr rexpr}]
    (dyna-debug
     (let [exp-vars (exposed-variables rexpr)
           set-vars (union (into #{} (for [i (range (+  1 arity))]
                                       (make-variable (str "$" i))))
                           (when-not (dnil? dynabase)
                             #{(make-variable "$self")}))]
       (when-not (and (subset? exp-vars set-vars)
                      (contains? exp-vars (make-variable (str "$" arity))))
         (debug-repl "add to user term error")
         (assert false)))
     (when-not (is-aggregator? rexpr)
       (debug-repl "adding without aggregator")))
    (let [[old-defs new-defs]
          (swap-vals! system/user-defined-terms (fn [old]
                                                  (let [v (get old object-name)
                                                        nv (if (nil? v)
                                                             (let [e (empty-user-defined-term object-name)]
                                                               (assoc e :rexprs (conj (:rexprs e) value)))
                                                             (do
                                                               ;;(invalidate! (:def-assumption v))
                                                               (assoc v
                                                                      :rexprs (conj (:rexprs v) value)
                                                                      :def-assumption (make-assumption))))
                                                        nv2 (if (not (dnil? dynabase))
                                                              (assoc nv :dynabases (conj (:dynabases nv #{}) dynabase))
                                                              nv)]
                                                    (assoc old object-name nv2))))
          assumpt (get-in old-defs [object-name :def-assumption])]
      ;; invalidate after the swap so that if something goes to the object, it will find the new value already in place
      (if assumpt (invalidate! assumpt)))))


(defn get-user-term [name]
  (let [sys (get @system/system-defined-user-term [(:name name) (:arity name)])]
    (if-not (nil? sys)
      {:builtin-def true
       :rexpr sys}
      (let [u (get @system/user-defined-terms name)
            another-file (:imported-from-another-file u)]
        (if another-file
          (recur another-file)
          u)))))

(defn- combine-user-rexprs [term-bodies]
  ;; this will combine multiple rexprs from a uesr's definition together
  ;; this should
  (context/bind-no-context ;; this is something that should be the same regardless of whatever nested context we are in
   (if (= 1 (count term-bodies))
     (:rexpr (first term-bodies))
     (let [out-vars (try (into #{} (map #(:result (:rexpr %))
                                        term-bodies))
                         (catch AssertionError e (debug-repl "assert error")))
           grouped (group-by (fn [rexpr]
                               (if (is-aggregator? rexpr)
                                 (:operator rexpr)))
                             (map :rexpr term-bodies))
           strip-agg (fn [in-var r]
                       (if (is-aggregator? r)
                         (remap-variables-handle-hidden (:body r)
                                          {(:incoming r) in-var})
                         r))
           make-aggs (fn [op out-var in-var rexprs]
                       (let [res
                             (make-aggregator op out-var in-var
                                              true ;; the body is conjunctive, meaning that we can move constraints out
                                              (make-disjunct (doall rexprs)))]
                         res))

           groupped-aggs (into {} (for [[op children] grouped]
                                    (if (= 1 (count children))
                                      (first children)
                                      (let [new-in (make-variable (gensym 'comb_incoming_var))
                                            new-children (for [c children]
                                                           (strip-agg new-in c))]
                                        [op (make-aggs op (first out-vars) new-in new-children)]))))]

       ;; if there is more than 1 group, then that means there are multiple aggregators, in which case we are going to have to have "two levels" of
       ;; aggregation created as a result.  This will
       (if (> (count groupped-aggs) 1)
         (let [intermediate-var (make-variable (gensym 'comb2_incoming_var))]
           (make-aggs "only_one_contrib" (first out-vars) intermediate-var
                      (map #(remap-variables-handle-hidden % {(first out-vars) intermediate-var}) (vals groupped-aggs))))
         (first (vals groupped-aggs)))))))


(def-rewrite
  :match (user-call (:unchecked name) (:unchecked var-map) (#(< % @system/user-recursion-limit) call-depth) (:unchecked parent-call-arguments))
  (let [ut (get-user-term name)]
    (when (nil? ut)
      (debug-repl "nil user term")
      (dyna-warning (str "Did not find method " (:name name) "/" (:arity name) " from file " (:source-file name))))

    (when ut  ;; this should really be a warning or something in the case that it can't be found. Though we might also need to create some assumption that nothing is defined...
      (let [rexprs (:rexprs ut)
            rexpr (combine-user-rexprs rexprs)
            rewrite-user-call-depth (fn rucd [rexpr]
                                      (dyna-assert (rexpr? rexpr))
                                      (if (is-user-call? rexpr)
                                        (let [[lname lvar-map lcall-depth] (get-arguments rexpr)
                                              new-call (make-user-call lname lvar-map (+ call-depth lcall-depth 1)
                                                                       #{})]
                                          (when-not (rexpr? new-call)
                                            (debug-repl "call fail rexpr"))
                                          ;(debug-repl)
                                          new-call)
                                        (let [ret (rewrite-rexpr-children rexpr rucd)]
                                          (when-not (rexpr? ret) (debug-repl "call fail rexpr"))
                                          ret)))
            ;; all-variables (get-all-variables-rec rexpr)
            ;; var-map-all (merge
            ;;              (into {} (remove nil? (for [k all-variables]
            ;;                                      (when-not (contains? k var-map)
            ;;                                        ;; these remapped variables could just be a unique object, where the object
            ;;                                        ;; would use its hascode and define equals as the identity.
            ;;                                        ;; but that would prevent it from creating a representation for the variable that could be used later
            ;;                                        ;; so maybe keeping this something that can be represented as clojure code is better
            ;;                                        [k (make-variable (gensym 'remaped-var))]))))
            ;;              var-map)
            ;; variable-map-rr-old (context/bind-no-context
            ;;                  (remap-variables
            ;;                   (rewrite-user-call-depth rexpr)
            ;;                   var-map-all))
            variable-map-rr (context/bind-no-context
                             (remap-variables-handle-hidden (rewrite-user-call-depth rexpr)
                                                            var-map))]

        (depend-on-assumption (:def-assumption ut))  ;; this should depend on the representational assumption or something.  Like there can be a composit R-expr, but getting optimized does not have to invalidate everything, so there can be a "soft" depend or something
        (dyna-debug (let [exp-var (exposed-variables variable-map-rr)]
                      (when-not (subset? exp-var (set (vals var-map)))
                        (debug-repl "should not happen, extra exposed variables"))))
        variable-map-rr))))
