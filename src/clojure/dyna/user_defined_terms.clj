(ns dyna.user-defined-terms
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.context :as context])
  (:require [dyna.assumptions :refer [invalidate! make-assumption make-invalid-assumption depend-on-assumption compute-with-assumption]])
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
   :optimized-rexpr-assumption (make-invalid-assumption) ;; if the optimized R-expr changes, this assumption needs to be invalidated

   :has-with-key false ;; if $with_key wraps the results of the term, in which case $value needs to be added to it when accessing the result

   :is-not-memoized-null (make-assumption) ;; if there is a memo table which _must_ be read, then this assumption should be made invalid
   :is-memoized-null (make-invalid-assumption)

   :is-memoized-unk (make-invalid-assumption)

   :memoization-mode :none  ;; should either be :none, :null or :unk depending

   ;:optimized-assumption (make-assumption) ;; the assumption that there is no more optimized version of this term
   ;:memoized-assumption (make-assumption) ;; if there is some changed to the memoized value for this term

   ;; if there are macros, then those are going to want to reference the files that they are coming from then I suppoes
   ;; this can check the from_file information on any term which is created I suppose
   ;; if something is a macro, then that means that there are potentially new variables which get introduced?
   ;; but I suppose that can be allowed as long as this just adds in the new project statements
   :is-macro false ;; if this is a macro meaning that this should get called on the AST of some expression, must have that the dynabase not be true

   :dispose-arguments nil ;; if this requires that some of its arguments get quoted.  again require that the program is written such that there aren't already intermediate variables which exist

   :rexprs () ;; R-exprs which have to get merged to gether to represent this term

   :optimized-rexpr nil ;; the R-exprs already combined together and "simplified" (optimized) such that

   :memoized-rexpr nil ;; if the term is memoized, then this should be the correponding structure

   :dynabases #{} ;; a set of dynabases that appear on this term.  We might be able to use this to perform some kind of type inference between expressions
   :dynabases-assumptions (make-assumption)

   ;; if this is imported from somewhere else, then this is the entire name of that other declared object
   ;; this will then have to recurse in finding the other thing
   :imported-from-another-file nil

   ;; if something is a constraint, then we can eliminate multiple copies of the
   ;; same rule call on an expression.  To determine if something is a
   ;; constraint, this is going to depend on the internal expression.  if something is an aggregator, then it should be able to find that there are
   :is-constraint (make-invalid-assumption)


   ;; would be nice if there was some kind of return value type information as
   ;; well.  This would have to be something which is cached information I
   ;; suppose that it could look at the various R-exprs which are defined for a
   ;; given term and use that information to identify which expression
   ;; correspond with something

   ;; there should be other fields here which correspond with memoized values or
   :term-name name})


(defn update-user-term! [name function]
  (let [[old new](swap-vals! system/user-defined-terms
                             (fn [old]
                               (let [v (get old name nil)]
                                 (assoc old name (function (if-not (nil? v) v (empty-user-defined-term name)))))))]
    [(get old name) (get new name)]))

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
                                                              (assoc nv
                                                                     :dynabases (conj (:dynabases nv #{}) dynabase)
                                                                     :dynabases-assumptions (make-assumption))
                                                              nv)]
                                                    (assoc old object-name nv2))))
          assumpt (get-in old-defs [object-name :def-assumption])
          assumpt-db (get-in old-defs [object-name :dynabases-assumptions])]
      ;; invalidate after the swap so that if something goes to the object, it will find the new value already in place
      (when assumpt
        (invalidate! assumpt))
      (if (and (not (nil? assumpt-db)) (not (identical? assumpt-db (get-in new-defs [object-name :dynabases-assumptions]))))
        (invalidate! assumpt-db)))))

(defn get-user-term [name]
  (let [sys-name [(:name name) (:arity name)]
        sys (get @system/system-defined-user-term sys-name)]
    (if-not (nil? sys)
      {:builtin-def true
       :rexpr sys}
      (let [gterm (get @system/globally-defined-user-term sys-name)]
        (if (and (not (nil? gterm)) (not= (:name gterm) name))
          (do ;(debug-repl)
            (recur (:name gterm)))
          (let [u (get @system/user-defined-terms name)
                another-file (:imported-from-another-file u)]
            (if another-file
              (recur another-file)
              (if (nil? u)
                (do
                  ;; printing a waring here does not work, as recursive functions will call themselves before they are fully defined
                  ;;(dyna-warning (str "Did not find method " (:name name) "/" (:arity name) " from file " (:source-file name)))

                  (get ;; if the term is not found, then we are going to create an
                   ;; empty term.  This will have mult 0, but assumptions
                   ;; which allow it to be overriden later
                   (swap! system/user-defined-terms (fn [x]
                                                      (if (contains? x name)
                                                        x
                                                        (assoc x name (empty-user-defined-term name)))))
                   name))
                u))))))))
(intern 'dyna.rexpr-constructors 'get-user-term get-user-term)

(defn- combine-user-rexprs-bodies [term-bodies]
  ;; this will combine multiple rexprs from a uesr's definition together
  ;; this should
  (context/bind-no-context ;; this is something that should be the same regardless of whatever nested context we are in
   (case (count term-bodies)
     0 (make-multiplicity 0)
     1 (:rexpr (first term-bodies))
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
                                              (make-disjunct (vec rexprs)))]
                         res))
           groupped-aggs (into {} (for [[op children] grouped]
                                    (if (= 1 (count children))
                                      [op (first children)]
                                      (let [new-in (make-variable (gensym 'comb_incoming_var))
                                            new-children (for [c children]
                                                           (strip-agg new-in c))]
                                        [op (make-aggs op (first out-vars) new-in new-children)]))))]
       (assert (= 1 (count out-vars))) ;; the out var should have the same name as we have standarized the names of the arguments

       ;; if there is more than 1 group, then that means there are multiple aggregators, in which case we are going to have to have "two levels" of
       ;; aggregation created as a result.  This will
       (if (> (count groupped-aggs) 1)
         (let [intermediate-var (make-variable (gensym 'comb2_incoming_var))]
           (make-aggs "only_one_contrib" (first out-vars) intermediate-var
                      (map #(remap-variables-handle-hidden % {(first out-vars) intermediate-var}) (vals groupped-aggs))))
         (first (vals groupped-aggs)))))))

(defn optimize-user-term [term-rep]
  (let [unopt-rexpr (combine-user-rexprs-bodies term-rep)
        [assumpt optimized] (binding [system/user-recursion-limit (min system/user-recursion-limit 5)]
                              (compute-with-assumption
                               (simplify-top unopt-rexpr)))])
  (debug-repl "optimize user term")
  (???)
  (assoc term-rep
         ))

(defn user-rexpr-combined-no-memo [term-rep]
  ;; this should check if there is some optimized
  (assert (nil? (:optimized-rexpr term-rep)))
  (depend-on-assumption (:def-assumption term-rep))
  (combine-user-rexprs-bodies (:rexprs term-rep)))

(defn user-rexpr-combined [term-rep]
  (if (:builtin-def term-rep)
    (:rexpr term-rep)
    (case (:memoization-mode term-rep)
      :none (do
              (depend-on-assumption (:is-not-memoized-null term-rep)) ;; memization of unk is fine, but null requires that we redo all of the computation
              (user-rexpr-combined-no-memo term-rep))
      :unk (do
             (depend-on-assumption (:is-memoized-unk term-rep))
             (:memoized-rexpr term-rep))
      :null (do
              (depend-on-assumption (:is-memoized-null term-rep))
              (:memoized-rexpr term-rep)))))



(def-rewrite
  :match (user-call (:unchecked name) (:unchecked var-map) (#(< % @system/user-recursion-limit) call-depth) (:unchecked parent-call-arguments))
  (let [ut (get-user-term name)]
    #_(when (nil? ut)
      (debug-repl "nil user term")
      (dyna-warning (str "Did not find method " (:name name) "/" (:arity name) " from file " (:source-file name))))
    (when (and (empty? (:rexprs ut)) (= :none (:memoization-mode ut)))
      (dyna-warning (str "Did not find method " (:name name) "/" (:arity name) " from file " (:source-file name))))

    (let [existing-parent-args (get parent-call-arguments name #{})
          local-map (into {} (for [[k v] var-map]
                               [k (get-value v)]))
          amapped (into #{} (for [s existing-parent-args]
                              (into {} (for [[k v] s]
                                         [k (get-value v)]))))]
      ;; this should really be a warning or something in the case that it can't be found. Though we might also need to create some assumption that nothing is defined...
      (when (and ut (not (contains? amapped local-map)))
        (let [new-parent-args (assoc parent-call-arguments name (conj (get parent-call-arguments name #{})
                                                                      var-map))
              rexpr (user-rexpr-combined ut)
              rewrite-user-call-depth (fn rucd [rexpr]
                                        (dyna-assert (rexpr? rexpr))
                                        (if (is-user-call? rexpr)
                                          (let [[lname lvar-map lcall-depth] (get-arguments rexpr)
                                                new-call (make-user-call lname
                                                                         lvar-map
                                                                         (+ call-depth lcall-depth 1)
                                                                         new-parent-args)]
                                            (when-not (rexpr? new-call)
                                              (debug-repl "call fail rexpr"))
                                            new-call)
                                          (let [ret (rewrite-rexpr-children rexpr rucd)]
                                            (when-not (rexpr? ret) (debug-repl "call fail rexpr"))
                                            ret)))
              [new-var-map with-key-var] (if (and (:has-with-key ut) (not (contains? var-map (make-variable "$do_not_use_with_key"))))
                                           (let [wkv (make-variable (gensym 'with-key-var))]
                                             [(assoc var-map (make-variable (str "$" (:arity name))) wkv) wkv])
                                            [var-map nil])
              variable-map-rr (context/bind-no-context
                               (remap-variables-handle-hidden (rewrite-user-call-depth rexpr)
                                                              new-var-map))]

          (depend-on-assumption (:def-assumption ut)) ;; this should depend on the representational assumption or something.  Like there can be a composit R-expr, but getting optimized does not have to invalidate everything, so there can be a "soft" depend or something
          (dyna-debug (let [exp-var (exposed-variables variable-map-rr)]
                        (when-not (subset? exp-var (set (vals new-var-map)))
                          (debug-repl "should not happen, extra exposed variables"))))
          (if-not (nil? with-key-var)
            (let [result-var (get var-map (make-variable (str "$" (:arity name))))
                  value-call (make-user-call {:name "$value" :arity 1}
                                             {(make-variable "$0") with-key-var
                                              (make-variable "$1") result-var}
                                             0
                                             {})
                  ret (make-proj with-key-var
                                 (make-conjunct [variable-map-rr
                                                 value-call]))]
              ret)
            variable-map-rr))))))


;; get a user defined function and turn it into something which can be called
;; not 100% sure that this should be included in this file.  Should maybe also
;; allow for there to be a textual representation that can be called into.  But
;; that is going to have to go through the parser first.
#_(defn get-user-defined-function [term-name arity]
  (fn [& args]
    (assert (= arity (count args)))
    (let [result-var (make-variable 'Result)
          rexpr (make-user-call term-name
                                (merge (into {} (for [[k v] (zipseq (range) args)]
                                                  [(make-variable (str "$" k)) (make-constant v)]))
                                       {(make-variable (str "$" arity)) result-var})
                                0
                                {})
          ctx (context/make-empty-context rexpr)
          result-rexpr (context/bind-context-raw ctx (simplify-fully rexpr))]
      (assert (= (make-multiplicity 1) (result-rexpr)))
      (ctx-get-value ctx result-var))))
