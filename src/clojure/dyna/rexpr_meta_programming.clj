(ns dyna.rexpr-meta-programming
  (:require [dyna.utils :refer :all])
  (:require [dyna.rexpr :refer :all])
  (:require [dyna.user-defined-terms :refer [def-user-term]])
  (:require [dyna.base-protocols :refer :all])
  (:import [dyna DynaTerm Dynabase])
  ;(:import [dyna.base_protocols Dynabase])
  (:import [dyna.rexpr unify-structure-rexpr]))

(def-base-rexpr indirect-user-call [:var indirect-user-var
                                    :var-list argument-vars
                                    :var result]
  (check-rexpr-basecases [this stack]
                         1 ;; indicate that there is an indirect user call, so we can't be sure about this
                         )
  (rexpr-jit-info [this] {:jittable false})
  (rexpr-jittype-hash [this] 0))

(def-base-rexpr reflect-structure [:var out
                                   :var dynabase
                                   ;;:var source-file ;; this needs to somehow reflect where the structure was created.
                                   :var name
                                   :var arity
                                   :var arguments])


(eval `(do ~@(for [i (range 1 50)]
               (let [vars (map #(symbol (str "v" %)) (range 1 (+ 1 i)))]
                 `(def-user-term "$call" ~i (make-indirect-user-call ~'v0 ~(vec (drop-last vars)) ~(last vars)))))))

;; $reflect(&foo(1,2,3), Name, Args) => (Name="foo")*(Args=[1,2,3]).

(def reflect-ignore-arg (make-constant (Object.)))  ;; a special value which indicates that the dynabase should just get ignored

;; maybe the $reflect/3 should just have $nil dynabase instead of allowing it to
;; unify with any dynabase.  So if something attempts to reflect when there is a
;; dynabase, it would just result in it failing, which is a bit more consistent behavior

(let [junk-arity (make-variable (gensym))]
  (def-user-term "$reflect" 3 (make-conjunct [(make-unify v3 (make-constant true)) ;; reflect always return true
                                              (make-proj junk-arity
                                                         (make-reflect-structure v0
                                                                                 reflect-ignore-arg ;; the dynabase that is associated with this term
                                                                                 v1
                                                                                 junk-arity ;; the arity is just an integer which should match the list length
                                                                                 v2))]))

  (def-user-term "$reflect" 4 (make-conjunct [(make-unify v4 (make-constant true))
                                              (make-proj junk-arity
                                                         (make-reflect-structure v0
                                                                                 v1
                                                                                 v2
                                                                                 junk-arity
                                                                                 v3))])))
(def-user-term "$reflect" 5 (make-conjunct [(make-unify v5 (make-constant true))
                                            (make-reflect-structure v0
                                                                    v1
                                                                    v2
                                                                    v3
                                                                    v4)]))


(def-rewrite
  :match (reflect-structure (:ground struct) (:any dynabase) (:any name) (:any arity) (:any arguments))
  (let [^DynaTerm struct-val (get-value struct)]
    (if-not (instance? DynaTerm struct-val)
      (make-multiplicity 0) ;; the struct variable is something else
      (let [ret (make-conjunct [(if (= dynabase reflect-ignore-arg)
                                  (make-multiplicity 1)
                                  (make-unify dynabase (make-constant (.dynabase struct-val))))
                                (make-unify name (make-constant (.name struct-val)))
                                (make-unify arity (make-constant (.arity struct-val)))
                                (make-unify arguments (make-constant (DynaTerm/make_list (.arguments struct-val))))])]
        ret))))

;; only use these on free, as otherwise it would be better to use the above rewrite
(def-rewrite
  :match (reflect-structure (:free struct) (:ground dynabase) (:ground name) (:any arity) (:ground arguments))
  (let [db-val (get-value dynabase)
        name-val (get-value name)
        arguments-val (get-value arguments)]
    (if-not (and (or (= dynabase reflect-ignore-arg) (instance? Dynabase db-val))
                 (instance? String name-val)
                 (instance? DynaTerm arguments-val))
      (make-multiplicity 0)
      (let [arguments-vec (.list_to_vec ^DynaTerm arguments-val)]
        (if (nil? arguments-vec)
          (make-multiplicity 0)
          (make-conjunct [(make-unify struct (make-constant (DynaTerm. name-val
                                                                       (if (= dynabase reflect-ignore-arg)
                                                                         DynaTerm/null_term
                                                                         db-val)
                                                                       nil ;; the filename that this term comes from might be relevant in the case
                                                                       arguments-vec)))
                          (make-unify arity (make-constant (count arguments-vec)))]))))))

(defn- arg-list [var remains cb]
  (if (empty? remains)
    (make-conjunct [(make-unify var (make-constant DynaTerm/null_term))
                    cb])
    (let [new-var (make-variable (gensym))]
      (make-proj new-var (make-conjunct [(make-unify-structure var nil (make-constant DynaTerm/null_term)
                                                               "." [(car remains) new-var])
                                         (arg-list new-var (cdr remains) cb)])))))

;; there needs to be a bit more which handles the resulting projects which are added when it will get the structure together
(def-rewrite
  :match (reflect-structure (:free struct) (:any dynabase) (:ground name) (:ground arity) (:any arguments))
  (let [name-val (get-value name)
        arity-val (get-value arity)]
    (if-not (and (string? name-val)
                 (int? arity-val))
      (make-multiplicity 0)
      (let [arg-vars (vec (for [_ (range arity-val)]
                            (make-variable (gensym))))]
        (arg-list arguments arg-vars (make-unify-structure struct
                                                           nil
                                                           dynabase
                                                           name-val
                                                           arg-vars))))))


(def-rewrite
  :match (indirect-user-call (:ground call-ref) (:any-list arguments) (:any result))
  (let [^DynaTerm call-ref-val (get-value call-ref)]
    (if-not (instance? DynaTerm call-ref-val)
      (make-multiplicity 0)
      (let [value-map (merge
                       (into {} (for [[i v] (zipseq (range) (.arguments call-ref-val))]
                                  [(make-variable (str "$" i)) (make-constant v)]))
                       (if-not (dnil? (.dynabase call-ref-val)) {(make-variable "$self") (make-constant (.dynabase call-ref-val))})
                       (into {} (for [[i v] (zipseq (range) arguments)]
                                  [(make-variable (str "$" (+ i (.arity call-ref-val)))) v]))
                       {(make-variable (str "$" (+ (.arity call-ref-val) (count arguments)))) result})
            cname (if (dnil? (.dynabase call-ref-val))
                    (do (assert (not (nil? (.from_file call-ref-val))))
                        {:name (.name call-ref-val)
                         :arity (+ (.arity call-ref-val) (count arguments))
                         :source-file (.from_file call-ref-val)})
                    {:name (.name call-ref-val)
                     :arity (+ (.arity call-ref-val) (count arguments))})]
        (make-user-call
         cname
         value-map
         0
         {})))))


;; this looks a conjunctive constraints that we might not have yet evaluated yet to identify what function is going to be called
(def-rewrite
  :match {:rexpr (indirect-user-call (:free call-ref) (:any-list arguments) (:any result))
          :context (unify-structure foo (:unchecked file-name) (:any dynabase) (:unchecked name-str) (:any-list arguments2))
          }
  :run-at :inference
  (let [;vv (debug-repl "good mathc indirect")
        args (concat arguments2 arguments)
        has-dynabase (not (and (is-bound? dynabase) (dnil? (get-value dynabase))))
        call-name (if has-dynabase
                    {:name name-str
                     :arity (count args)}
                    {:name name-str
                     :arity (count args)
                     :source-file file-name})
        value-map (merge (into {} (for [[i v] (zipseq (range) args)]
                                    [(make-variable (str "$" i)) v]))
                         (when has-dynabase {(make-variable "$self") dynabase})
                         {(make-variable (str "$" (count args))) result})]
    (make-user-call call-name value-map 0 {})))

#_(def-rewrite
  :match (indirect-user-call (:free call-ref) (:any-list arguments) (:any result))
  :run-at :inference
  (let []
    (debug-repl "indirect inference")
    nil))
