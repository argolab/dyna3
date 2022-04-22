(defproject dyna "0.1.0-SNAPSHOT"
  :description "Dyna built on R-exprs"
  :url "https://github.com/argolab/dyna3"
  :license {:name "LGPL-3.0-or-later WITH Classpath-exception"}
  :dependencies [[org.clojure/clojure "1.11.1" ;"1.12.0-mfl-SNAPSHOT"
                  ]
                 [org.clojure/tools.namespace "1.2.0"]
                 [aprint "0.1.3"]  ;; for formatted printing
                 ;[clj-python/libpython-clj "2.00-beta-22"]
                 [com.clojure-goes-fast/clj-java-decompiler "0.3.0"] ;; for debugging what the generated code looks like
                 [org.antlr/antlr4-runtime "4.7.2"] ;; for the front end parser
                 [org.jline/jline "3.20.0"]  ;; for the front end repl
                 [robert/hooke "1.3.0"]
                 ;[jise "0.1.0-SNAPSHOT"] ;; can get more control over the generated java classes
                 ;[datalevin "0.6.6"]
                 [org.clojure/tools.analyzer.jvm "0.7.3"]
                 ]
  :repl-options {:init-ns dyna.core}
  ;; :aot [dyna.interface
  ;;       dyna.parser_interface]
  ;;:aot :all
  ;;:aot [dyna.rexpr]
  :source-paths ["src/clojure"]
  :java-source-paths ["target/gen-src" "src/java"]
  :resource-paths ["src/resources"]
  :test-paths ["test"]
  ;:profiles {:uberjar {:aot :all}}
  ;;:profiles {:uberjar {:aot [dyna.rexpr]}}
  :plugins [[lein-antlr-plugin "0.1.0"]
            [me.shalakapatil/retest-failures "0.1.0-SNAPSHOT" :hooks false]]
  :antlr-src-dir "src/antlr"
  :antlr-dest-dir "target/gen-src"

  :profiles {:uberjar {:main dyna.DynaMain
                       ;:aot [dyna.core] ;; this makes it start faster but run slower....
                       }}
  :main dyna.core

  ;; this is needed to generate the uberjar, but it makes it slower to run when working on stuff
  ;; so can comment out if running tests or something from the local directory
  :aliases {"compile" ["do" ["antlr"] ["javac"] "compile"]
            "uberjar" ["do" ["compile"] "uberjar"]}


  ;;:main dyna.DynaMain
  :global-vars {;*warn-on-reflection* true  ;; useful for identifying where it uses clojure's reflection which is slow...
                                        ;*unchecked-math* :warn-on-boxed ;; boxed math is slow9
                }

   :repositories [["matthewfl.com" "https://matthewfl.com/maven-repo"]]
  )
