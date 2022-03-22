(comment
  (ns dyna.trie-test
    (:require [clojure.test :refer :all])
    (:require [dyna.prefix-trie :refer :all]))


  (deftest make-trie
    (make-prefixtrie 10)))
