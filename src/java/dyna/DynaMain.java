package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Var;

class DynaMain {
    public static final long starting_time = System.currentTimeMillis();

    public static void main(String[] args) {
        // the time to first print is quite long, if we wanted, we could start the compilation in a thread
        // and just print the "normal" stuff for the first few seconds while waiting for the compile to complete in the thread
        // it would have to have some blocking methods before it would be allowed to call into the runtime

        initRuntime();

        IFn main_function = Clojure.var("dyna.core", "main"); // invoke the main method with the arguments now
        main_function.invoke(args);
    }

    public static void initRuntime() {
        // anything about setting up the clojure runtime before we begin or loading the files should be done here
        // then we can call this from other places which might serve as entry points to the runtime
        if("true".equals(System.getProperty("dyna.unchecked_math"))) {
            ((Var)Clojure.var("clojure.core", "*unchecked-math*")).bindRoot(true);
        }

        Clojure.var("clojure.core", "load").invoke("/dyna/core"); // load and compile all of the files
    }
}
