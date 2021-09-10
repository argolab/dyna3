(ns dyna-backend.aggregators
  (:require [dyna-backend.rexpr :refer :all])
  (:require [dyna-backend.rexpr-builtins :refer [DynaMap make-lessthan make-lessthan-eq]]))

(def aggregators (atom {}))

(defm def-aggregator [name & args]
  (let [kw-args (apply hash-map args)]
    ;; this should construct the other functions if they don't already exist, so that could mean that there are some defaults for everything
    ;; when the aggregator is created, it can have whatever oeprations are
    (swap! aggregators name (assoc kw-args :name name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(def-aggregator "+="
  :combine +)

(def-aggregator "*="
  :combine *)


;; we can define 'advanced' aggregators which will allow this to pass through
;; some information, something like all of the values will be >= 0, in which
;; case we can take whatever is the current value as an upper bound.  Could then
;; propose that there could be rewrites which annotate that the result of some
;; expression will be positive, in which case it could "convert" from one
;; aggregator to another or something.  This would allow for it to somehow focus
;; its time on branches which are going to be the most useful.
(comment (def-aggregator "prob+="
           :combine +))

(def-aggregator "="
  ;; in the case that there are two different, then that is an error, though not 100% sure where the unification failure is going to pop up in this case???
  :combine (fn [a b]
             (if (not= a b)
               (throw (UnificationFailure. "The equals aggregator (=) requires only one contribution")))
             a))


(def- get-aggregated-value [v]
  (if (and (instance? structured-term-value v) (= (.name ^structured-term-value v) "$with_key_pair"))
    (get (.arguments ^structured-term-value v) 1)
    v))


;; maybe the add-to-rexpr-incoming should take an R-expr rather than just taking
;; whatever is the current value to the expression.  In the case that there is
;; an R-expr, that would make the representation of the expression a bit easier
;; for the compiler to work with rather than an opaque function which it can't
;; observe?  Though with the function, it could just use that to construct the
;; R-expr and then it can just keep the R-expr around?  So that would allow it
;; to avoid having to have some lambda names or something.  I suppoose that it
;; could have some current value expression with this looking through

(def-aggregator "max="
  :combine (fn [a b] (if (> (get-aggregated-value a) (get-aggregated-value b)) a b))
  :allows-with-key true
  ;; this will let us add expressions to the R-expr so that this can eleminate branches which are not useful
  :add-to-rexpr-incoming (fn [current-value incoming-variable]  ;; this would mean that there needs to be some optional stuff for these, or some way in which assumptions can be tracked for these branches.  We don't want to store these expressions in the case that
                           (make-lessthan-eq (make-constant current-value) incoming-variable))
  :add-to-rexpr-result (fn [current-value result-variable]
                         (make-lessthan-eq (make-constant current-value) result-variable))
  )

(def-aggregator "min="
  :combine (fn [a b] (if (< (get-aggregated-value a) (get-aggregated-value b)) a b))
  :allows-with-key true
  ;; this add-to-rexpr will have to know if with-key is included in the expression.
  ;; this would mean that it somehow removes the unification in the case
  :add-to-rexpr-incoming (fn [current-value incoming-variable]
                           (make-lessthan-eq incoming-variable (make-constant current-value)))
  ;; adding some information to the result of the expression would allow for
  ;; this to indicate that the resulting value will at least be greater than
  ;; what the current expression is.  having some lessthan expression added on
  ;; the result side will allow for this to replicate alpha-beta pruning as a
  ;; strategy These lessthan expressions should then be able to combine together
  ;; to eleminate branches
  :add-to-rexpr-result (fn [current-value result-variable]
                         (make-lessthan-eq result-variable (make-constant current-value))))

(def-aggregator ":-"
  :combine (fn [a b] (or a b))
  :saturate #(= true %))
;; this aggregator is already going to have that the incoming variable is unified with the expression which corresponds with

(def-aggregator "|="
  :combine (fn [a b] (or a b))
  :saturate #(= true %)
  :add-to-rexpr (fn [current-value incoming-variable]
                  (if (= current-value false)
                    (make-unify incoming-variable (make-constant true)))))

(def-aggregator "&="
  :combine (fn [a b] (and a b))
  :saturate #(= false %)
  :add-to-rexpr (fn [current-value incoming-variable]
                  (if (= current-value true)
                    ;; then this could add some unify the result with false as that is the only thing which can change the value of this expression
                    ;; but could that causes this expression to run something that wouldn't have run otherwise?
                    (make-unify incoming-variable (make-constant false)))))

;; a global counter which is used for all := across the entire program in the
;; case of nested dynabases, this will not necessarily allow for overriding a
;; value with another expression as this will not know the "order" in which expressions are contributed
(def ^:private colon-equals-counter (atom 0))
(defn get-colon-equals-count [] (swap! colon-equals-counter inc))

(def-aggregator ":="
  :combine (fn [a b]
             (let [[la va] (.arguments ^structured-term-value a)
                   [lb vb] (.arguments ^structured-term-value b)]
               (if (> lb la) b a)))
  :check-input (fn [x]
                 (and
                  (instance? structured-term-value x)
                  (= "$colon_line_tracking" (.name ^structured-term-value x))))
  :add-to-rexpr (let [linevar (make-variable (gensym))
                      valvar (make-variable (gensym))]
                  (fn [current-value incoming-variable]
                    (let [[line val] (.arguments ^structured-term-value current-value)]
                      (make-proj-many [linwvar valvar] (make-conjunct [
                                                                       (make-unify-structure incoming-variable (make-constant nil)
                                                                                             "$colon_line_tracking" [linevar valvar])
                                                                       (make-lessthan-eq (make-constant line) linevar)]))))))


; this should merge a map together.  This would not have which of the expressions would
(def-aggregator "merge="
  :combine merge
  :check-input (partial instance? DynaMap))

(def-aggregator "?="
  :combine (fn [a b] a) ;; we just have to choose something
  :saturate (fn [x] true)  ;; this saturates once it gets something, so we can
                           ;; just ignore whatever value is selected, we don't
                           ;; have to keep running this value.  Having this as a
                           ;; function means that we can make this do whatever
                           ;; we want with the representation
  )
