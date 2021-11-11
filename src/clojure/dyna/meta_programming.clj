(ns dyna.meta-programming
  (:reuqire [dyna.rexpr :refer :all])
  )

(comment

  ;; there should be some meta-programming operations


  (def-base-rexpr indirect-user-call [:var indirect-user-var
                                      :var-list argument-vars
                                      :var result])

(doseq [i (range 1 50)]
  (let [vars (map #(symbol (str "v" %)) (range 1 (+ 1 i)))]
    (eval `(def-user-term "$call" ~i (make-indirect-user-call ~'v0 ~(vec (drop-last vars)) ~(last vars))))))


(def-base-rexpr reflect-structure [:var out
                                   :var dynabase
                                   :var name
                                   :var arity ;; once the name and arity is known, then this can be replaced as a bunch of unify expressions
                                   :var arguments])


(let [junk-var (make-variable (gensym))]
  (def-user-term "$reflect" 3 (make-proj junk-var
                                         (make-conjunct [(make-unify v3 (make-constant true))
                                                         (make-proj junk-var (make-reflect-structure v0 self v1 junk-var v2))]))))

(def-user-term "$reflect" 4 (make-conjunct [(make-unify v4 (make-constant true))
                                            (make-reflect-structure v0 self v1 v2 v3)]))

;; (def-base-rexpr reflect-structure-vlist [:var out
;;                                          :var dynabase
;;                                          :var name ;; the name just needs to be known, and then we can just replace the expression
;;                                          :var-list arguments])

;; (doseq [i (range 1 10)]
;;   (let [vars (map #(symbol (str "v" %)) (range 1 (+ 1 i)))]
;;     `(eval (def-user-term "$structure" i ~(last vars) ~'self ~'v0 ~(vec (rest (drop-last vars)))))))


(def-rewrite
  :match (reflect-structure (:ground out) (:any dynabase) (:any name) (:any arity) (:any arguments))
  (let [structure (get-value out)]
    (if (instance? DynaTerm structure)
      (make-conjunct [(make-unify dynabase (make-constant (.dynabase ^DynaTerm structure)))
                      (make-unify name (make-constant (.name ^DynaTerm structure)))
                      (make-unify arity (make-constant (.arity ^DynaTerm structure)))
                      (make-unify arguments (make-constant (DynaTerm/make_list (.arguments ^DynaTerm structure))))])
      )
    (make-multiplicity 0)))

(def-rewrite
  :match (reflect-structure (:any out) (:ground dynabase) (:ground name) (:any arity) (:ground arguments))
  (let [db (get-value dynabase)
        n (get-value name)
        args (get-value arguments)
        ]
    (if (or (not (string? n)) (not (instance? DynaTerm args)))
      (make-multiplicity 0)
      (let [args-vals (.list_to_vec ^DynaTerm args)]
        (if (nil? args-vals)
          (make-multiplicity 0)
          ;; the reflect needs to also have the filename for the object, otherwise we can construct calls to the objects that we want
          ;; if a dynbase could also just dispatch to the filename or something, maybe we could allow for the dynabase to be either a dynabase or a filename
          ;; if there are
          )
      )
    )
    )
  )

  ;; there can be something like this structure would resemble which of the
  ;; expressions would correspond with the variables for a given expression.  this
  ;; will then have to figure out which variables are contextually present in the
  ;; expression, as the names of variables might change at a later point in time.
  ;; So there would probably have to be special handing around this expression.  I
  ;; suppose that this would also have to

  ;; (def-base-rexpr eval-user-form [:var Out
  ;;                                 :var structure])

  ;; (def-user-term "$eval" 1 (eval-user-form vv1 v0))


  ;; if indirect-user-call does not find the object which it is attempting to
  ;; call, then it should have that it reports some warning to the user so if
  ;; there is some missmatch between arguments.
  ;;

)
