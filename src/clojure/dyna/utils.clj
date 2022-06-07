(ns dyna.utils
  (:require [aprint.core :refer [aprint]])
  (:require [dyna.system :refer [debug-on-assert-fail debug-statements]])
  (:import [dyna DynaTerm]))

;; make functions like car caar cdr etc

(defn- make-cr-function-body [args]
  (if (= args "") 'x
      (case (subs args 0 1)
        "a" `(clojure.core/first ~(make-cr-function-body (subs args 1)))
        "d" `(clojure.core/rest ~(make-cr-function-body (subs args 1))))))

(defn- make-cr-function [args]
  `(defn ~(symbol (str "c" args "r")) ~'[x]
     ~(make-cr-function-body (apply str (reverse args)))))

(defn- make-function-depth [depth]
  (if (= depth 0) (list "")
      (for [l ["a" "d"]
            s (make-function-depth (- depth 1))]
        (str l s))))

;; doall forces the loop to not be lazy, which creates the functions
;; (doall (for [i (range 1 10)
;;              func (make-function-depth i)]
;;          (eval (make-cr-function func))))

(eval `(do ~@(for [i (range 1 10)
                   func (make-function-depth i)]
               (make-cr-function func))))


(defn ??? [] (throw (RuntimeException. "Not Implemented")))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; https://gist.github.com/ato/252421

(declare ^:dynamic *locals*)
(defmacro debugger-get-local-bindings
  "Produces a map of the names of local bindings to their values."
  []
  (let [symbols (map key @clojure.lang.Compiler/LOCAL_ENV)]
    (into {} (for [s symbols]
               ;; this removes type tag info which causes the compiler to choke on the information
               [`(quote ~s) (vary-meta s dissoc :tag)]))
    ;;res (zipmap (map (fn [sym] `(quote ~sym)) symbols) (map symbol symbols))
    ;;(aprint res)
    ;;res
    ;;     res `{}~@(apply concat (for [s symbols]
    ;;                              `((quote ~(symbol s)) ~(symbol s))))]
    ;; (print res)
    ;; res
        ))

(defn eval-with-locals
  "Evals a form with given locals.  The locals should be a map of symbols to
  values."
  [locals form]
  (binding [*locals* locals]
    (eval
     `(let ~(vec (mapcat #(list % `(*locals* '~%)) (keys locals)))
        ~form))))

;; the system.out might be getting messed with.  The system/in is not getting echoed back

(def debug-useful-variables (atom {'aprint (fn [] aprint)}))

(defn- debug-repl-fn [prompt local-bindings ^Throwable traceback]
  (let [all-bindings  (merge (into {} (for [[k v] @debug-useful-variables]
                                        [k (v)]))
                             (into {} (for [[k v] (ns-publics 'dyna.rexpr-constructors)]
                                        [k (var-get v)]))
                             (into {} (for [[k v] (ns-publics 'dyna.base-protocols)]
                                        [k (var-get v)]))
                             local-bindings)]
    (.printStackTrace traceback System/out)
    (try (aprint local-bindings)
         (catch Exception err nil))
    (clojure.main/repl
     :read (fn [fresh-request exit-request]
             (let [res (clojure.main/repl-read fresh-request exit-request)]
                                        ;(println "===========\n" res# "\n" (type res#) "\n==========")
               (cond (contains? #{'quit 'exit} res) (do (System/exit 0)
                                                        fresh-request)
                     (contains? #{'c 'continue} res) exit-request  ;; exit the eval loop
                     (contains? #{'bt 'backtrace} res) (do (.printStackTrace traceback System/out)
                                                           fresh-request)
                     (contains? #{'locals} res) (do (aprint local-bindings)
                                                    fresh-request)
                     (contains? #{'locals-names 'local-names} res) (do (print (keys local-bindings) "\n")
                                                                       fresh-request)
                     ;; TODO: this should attempt to lookup names in some context
                     :else res)))
     :prompt #(print prompt "=> ")
     :eval (partial eval-with-locals all-bindings))))


(defmacro debug-repl
  "Starts a REPL with the local bindings available."
  ([] `(debug-repl "dr"))
  ([prompt] `(~debug-repl-fn ~prompt (debugger-get-local-bindings) (Throwable. "Entering Debugger"))))

(defmacro debug-delay-ntimes [ntimes & body]
  (let [sym (gensym 'debug-delay)
        isym (intern *ns* sym 0)]
    `(do
       (alter-var-root ~isym inc)
       (when (>= @~isym ~ntimes)
         ~@body))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defn map-same-type [func val] ; I feel like this should be defined somewhere in the library???
  (cond (vector? val) (vector (map func val))
        (map? val) (into {} (map func val))
        (set? val) (into #{} (map func val))
        :else val))


(defn add-function-argument [functions argument body]
  (cond (list? body) (let [ags (map (partial add-function-argument functions argument) (cdr body))]
                       (if (contains? functions (car body))
                         (concat (list (car body) argument) ags)
                         (cons (car body) ags)))
        ;; though this map might return different types
        (or (vector? body) (set? body)) (map-same-type (partial add-function-argument functions argument) body)
        (map? body) (into {} (map (fn [[name b]] [name (add-function-argument functions argument b)]) body))
        :else body))



;; this function runs every call through resolve which thing it should be
;; though this does not improve the efficiency of the runtime at all as this still goes through with resolving lots of fields anytime it
;; attempts to call a function
(defn resolve-functions [body env]
  (cond (list? body)
        (concat (list (or (resolve env (car body)) (car body)))
                (map #(resolve-functions %1 env) (cdr body)))
        (vector? body) (vector (map #(resolve-functions %1 env) body))
        ;; there shouldn't be anything else that needs to get mapped here
        :else body))


;; if there is some function that can cache the result of some computation, then we can have a field that is nil
;; by default, and then run the function to store the result of the computation.
;; I suppose that this should allow for the function to be such that it
(defmacro cache-field [field & func]
  `(if (nil? ~field)  ;; if the field is an int, then the nil? check doesn't work
     (let [sr# (do ~@func)]
       (set! ~field sr#)
       ~field)
     ~field))



;; a macro for overriding functions in the body which also appear in the opts
;; this shoudl allow us to make it such that there is a generic function which
;; is called, but also something which will cause the values of the expression to corresponds
(defmacro override-functions [opts & bodies]
  (debug-repl)
  bodies)

(defmacro deftype-with-overrides
  [name args overrides & bodies]
  (let [override-map (into {} (for [o  overrides]
                                ;; using (name) as otherwise we might get a name which is already resolved in the namespace
                                [(symbol (clojure.core/name (car o))) o]))
        override-used (transient #{})
        ret (doall `(deftype ~name ~args
                      ~@(for [b bodies]
                          (if (and (seqable? b) (contains? override-map (car b)))
                            (do
                              (conj! override-used (car b))
                              (get override-map (car b)))
                            b))))]
    (let [override-used (persistent! override-used)]
      (when (not= (into #{} (keys override-map)) override-used)
        (debug-repl "failed override")))
    ret))


;; (defmacro deftype-with-overrides
;;   [name args overrides & bodies]
;;   )

;; (defn overrideable-function
;;   "Allows for a function in a macro to be overriden via the optional arguments"
;;   [opts name body]
;;   (let [ret (atom body)]
;;     (doseq [o opts]
;;       (if (= (car o) name)
;;         (reset! ret o)))
;;     @ret))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defn dnil? [x] (or (nil? x) (= DynaTerm/null_term x)))

(defn make-list [& x] (DynaTerm/make_list x))

(defn- make-term-fn [x]
  (if (and (seqable? x) (string? (first x)))
    `(DynaTerm/create_arr ~(first x) [~@(map make-term-fn (rest x))])
    x))

(defmacro make-term [x]
  (make-term-fn x))

(defn- match-term-fn [source-var match-expression body]
  (let [func-name (car match-expression)
        arity (- (count match-expression) 1)
        match-vars (vec (map #(if (symbol? %) % (gensym)) (cdr match-expression)))]
    `(when (and (instance? DynaTerm ~source-var)
                (= ~(str func-name) (.name ^DynaTerm ~source-var))
                (= ~arity (.arity ^DynaTerm ~source-var)))
       (let [~match-vars (.arguments ^DynaTerm ~source-var)]
         ~(reduce (fn [a b]
                    (if (nil? a)
                      b
                      (match-term-fn (get a 1) (get a 0) b)))
                  (conj (vec (map (fn [me var]
                                    (if (symbol? me)
                                      nil
                                      [me var]))
                                  (cdr match-expression)
                                  match-vars))
                        body))))))

(defmacro match-term [source-var match-expression & body]
  (let [svar (gensym 'source-term-var)]
    `(let [~svar ~source-var]
       ~(match-term-fn svar match-expression `(do ~@body)))))

(defmacro dyna-assert [expression]
  `(when-not ~expression
     (when debug-on-assert-fail
       (debug-repl ~(str "assert failed " expression)))
     (throw (AssertionError. ~(str "assert failed " expression)))))


(defmacro dyna-debug [& args]
  (if debug-statements ;(= "true" (System/getProperty "dyna.debug" "true"))
    `(do ~@args)))

(defmacro debug-try [& args]
  (if debug-statements
    `(try ~@args)
    (first args)))

(defmacro debug-binding [b & body]
  (if debug-statements;(= "true" (System/getProperty "dyna.debug" "true"))
    `(binding ~b ~@body)
    `(do ~@body)))

(def ^{:private true} warnings-shown-so-far (atom {}))

(defn dyna-warning [msg]
  (let [shown-count (get @warnings-shown-so-far msg 0)]
    (when (< shown-count 3)
      (swap! warnings-shown-so-far update msg (fnil inc 0))
      (println "=============================================")
      (println "WARNING" msg)
      (println "============================================="))))


;; the clojure protocols are a bit more heavy weight than Java interfaces, as
;; there is additional logic which allows them to be extended outside of the the
;; Java class mechnism.
;;
;; We don't really need that, so it should be possible to have something which
;; supports the clojure naming and variable scoping, but is simpler in that it
;; will just directly cast the type of the arguments to the correct intrerface

(defmacro defsimpleinterface [name & methods]
  (let [this-var (gensym)
        class-name (str (namespace-munge *ns*) "." name)]
    `(do (definterface ~name
           ~@(for [m methods]
               `(~(symbol (munge (first m))) ~(second m))))
         ~@(for [m methods]
             `(defn ~(first m)
                ;; this does not seem to generate the type annotation correctly..... so this does not become a direct call properly
                {:inline (fn [~this-var & args#]
                           (concat (list '. (with-meta ~this-var ~{:tag class-name})
                                         (quote ~(symbol (munge (first m)))))
                                   args#))}
                ~(into [this-var] (second m))
                (. ~(with-meta this-var {:tag class-name})
                   ~(symbol (munge (first m)))
                   ~@(second m))))
         ~name)))

;; this would have to make some interface for the methods or this could just
;; define methods which cast the type to the class, and then invoke

(comment
  (defmacro deflcass [name & methods+parent]
    nil))
