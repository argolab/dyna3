(ns dyna.user-defined-terms
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.system :as system])
  (:require [dyna.assumptions :refer [invalidate! make-assumption depend-on-assumption]])
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

(defn empty-user-defined-term []
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

   :imported-from-another-file nil ;; the reference to another file if this came from somewhere else.  This should be the qualified name of the object so it can go looking for whatever it is attempting to call.  This will not then have its own R-exprs defined, as it will require that there is some extension or something rather than adding additional information

   ;; would be nice if there was some kind of return value type information as
   ;; well.  This would have to be something which is cached information I
   ;; suppose that it could look at the various R-exprs which are defined for a
   ;; given term and use that information to identify which expression
   ;; correspond with something

   ;; there should be other fields here which correspond with memoized values or
   })

(defn update-user-term [name function]
  (swap! system/user-defined-terms (fn [old]
                                     (let [v (get old name)]
                                       (assoc old name (function (if v v (empty-user-defined-term))))))))

(defn add-to-user-term [source-file dynabase name arity rexpr]
  (let [object-name (merge {:name name
                            :arity arity}  ;; I suppose that there isn't going to be variable argument expressions, meaning that this will
                           (when (dnil? dynabase) ;; when there is a dynabase, then this requires having to merge across different values
                             {:source-file source-file}))
        value {:source-file source-file
               :dynabase dynabase
               :rexpr rexpr}]
    (let [[old-defs new-defs]
          (swap-vals! system/user-defined-terms (fn [old]
                                                  (let [v (get old object-name)
                                                        nv (if (nil? v)
                                                             (let [e (empty-user-defined-term)]
                                                               (assoc e :rexprs (conj (:rexprs e) value)))
                                                             (do
                                                               ;;(invalidate! (:def-assumption v))
                                                               (assoc v
                                                                      :rexprs (conj (:rexprs v) value)
                                                                      :def-assumption (make-assumption))))
                                                        nv2 (if (not (dnil? dynabase))
                                                              (assoc nv :dynabases (conj dynabase (:dynabases nv #{})))
                                                              nv)]
                                                    (assoc old object-name nv2))))
          assumpt (get-in old-defs [object-name :def-assumption])]
      ;; invalidate after the swap so that if something goes to the object, it will find the new value already in place
      (if assumpt (invalidate! assumpt)))))


(defn get-user-term [name]
  (let [r (or (get @system/system-defined-user-term [(:name name) (:arity name)])
              (get @system/user-defined-terms name))
        another-file (:imported-from-another-file r)]
    (if another-file
      (recur (assoc name :source-file another-file))
      r)))


(def-rewrite
  :match (user-call (:unchecked name) (:unchecked var-map) (#(< % @system/user-recursion-limit) call-depth))
  (let [ut (get-user-term name)]
    (when ut  ;; this should really be a warning or something in the case that it can't be found. Though we might also need to create some assumption that nothing is defined...
      (let [rexprs (:rexprs ut)
            rexpr (do
                    (assert (= (count rexprs) 1)) ;; todo, this is going to need to combine the R-exprs in the case that there are multiple.  This means that the user expression will have possibly many aggregators, as well as
                    (:rexpr (first rexprs)))
            rewrite-user-call-depth (fn rucd [rexpr]
                                      (when-not (rexpr? rexpr)
                                        (debug-repl))
                                      (if (is-user-call? rexpr)
                                        (do
                                          (debug-repl))
                                        (rewrite-rexpr-children rexpr rucd)))
            call-depth-rr (rewrite-user-call-depth rexpr)
            variable-map-rr (remap-variables call-depth-rr var-map)]
        (depend-on-assumption (:def-assumption ut))  ;; this should depend on the representational assumption or something.  Like there can be a composit R-expr, but getting optimized does not have to invalidate everything, so there can be a "soft" depend or something
        variable-map-rr))))
