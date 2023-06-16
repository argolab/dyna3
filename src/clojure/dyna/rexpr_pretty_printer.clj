(ns dyna.rexpr-pretty-printer
  (:require [dyna.utils :refer :all])
  (:require [dyna.base-protocols :refer :all]))

(def ^{:dynamic true} *print-variable-name* (fn [var]
                                              (:varname var)))

;; symbols that we will define and then handle ourselves when formatting the string
(defn optional-line-break []
  "\ufff0")
(defn indent-increase []
  "\ufff1")
(defn indent-decrease []
  "\ufff2")

;; the these are otiemes/oplus, but these symbols are hard to read in the terminal.  currently just using */+ but that is going to get confusing....
(defn symbol-conjunct []
  "\u2a02")

(defn symbol-disjunct []
  "\u2a01")

(defn- format-rexpr-string [^StringBuffer out target-width rexpr-str-seq]
  (let [current-line-length (volatile! 0)
        indent-stack (volatile! (list 0))]
    (loop [s rexpr-str-seq]
      (when-not (empty? s)
        (let [c (first s)]
          (case c
            \ufff0 (when (>= @current-line-length target-width)
                     (.append out "\n")
                     (.append out (apply str (repeat (first indent-stack) " ")))
                     (vreset! current-line-length (first indent-stack)))
            \ufff1 (vswap! indent-stack #(cons @current-line-length %))
            \ufff2 (vswap! indent-stack rest)
            (do
              (.append out c)
              (vswap! current-line-length inc)))
          (recur (rest s)))))))


(defmulti rexpr-printer type)

(defmethod rexpr-printer :default [rexpr]
  (debug-repl "default printer")
  (str rexpr))

(defn print-rexpr [rexpr & {:keys [width] :or {width 100}}]
  (let [s (rexpr-printer rexpr)
        sb (StringBuffer.)]
    (format-rexpr-string sb width (seq s))
    (.toString sb)))
