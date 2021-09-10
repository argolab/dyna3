(ns dyna-backend.func-metadata)

;; the idea being that functions should somehow have metadata which is represented on the function
;; can we determine which variables come from the clojure?  This would allow for it to somehow determine that there are
(defmacro fnm [args & body]
  `(with-meta (fn ~args ~body) {:args ~args :body (quote ~body)}))
