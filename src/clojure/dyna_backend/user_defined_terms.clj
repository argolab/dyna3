(ns dyna-backend.user-defined-terms
  (:require [dyna-backend.utils :refer :all])
  (:require [dyna-backend.rexpr :refer [make-variable]])
  (:require [dyna-backend.system :as system])
  (:require [dyna-backend.assumptions :refer [invalidate! make-assumption]]))


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

   :rexprs () ;; {:source-file nil, :dynabase nil, :rexpr nil}

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
                           (when (nil? dynabase) ;; when there is a dynabase, then this requires having to merge across different values
                             {:source-file source-file}))
        value {:source-file source-file
               :dynabase dynabase
               :rexpr rexpr}]
    (swap! system/user-defined-terms (fn [old]
                                       (let [v (get old object-name)
                                             nv (if (nil? v)
                                                  (let [e (empty-user-defined-term name arity)]
                                                    (assoc e :rexprs (conj (:rexprs e) value)))
                                                  (do
                                                    (invalidate! (:def-assumption v))
                                                    (assoc v
                                                           :rexpr (conj (:rexprs v) value)
                                                           :def-assumption (make-assumption))))
                                             nv2 (if dynabase
                                                   (assoc nv :dynabases conj dynabase)
                                                   nv)]
                                         (assoc old object-name nv2))))))

;; (defn user-add-to-user-expression [source-file dynabase name arity rexpr]
;;   (let [object-name (merge {:name name
;;                             :arity arity}
;;                            (when (nil? dynabase) ;; when there is a dynabase, then this requires having to merge across different values
;;                              {:source-file source-file}))
;;         value {:source-file source-file
;;                :dynabase dynabase
;;                :rexpr rexpr}]
;;     ;; add the object to the user-defined-terms
;;     (swap! system/user-defined-terms (fn [old]
;;                                        (let [v (get old object-name)]
;;                                          (assoc old object-name (conj v value)))))
;;     ;; invalidate the assumption that this values has not changed
;;     ;; we do the invalidation /after/ we have already made the change, a the reader has to first get the assumption
;;     ;; whereas the writer has to first write the object
;;     (swap! system/user-defined-assumptions (fn [old]
;;                                       (let [v (get old object-name)]
;;                                         (if v (invalidate! v))
;;                                         (assoc old object-name (make-assumption)))))
;;     )
;;   (debug-repl)
;;   (assert false)

;;   ;; if there is a dynabase, then this needs to be "global", otherwise we can get away with just dispatching on the source file info
;;   ;; if there are

;;   ;; define to the user level term from the external program
;;   )

;; (defn lookup-user-def [name arity]
;;   (get base-user-defs [name arity]))
