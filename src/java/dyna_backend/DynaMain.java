package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Var;

class DynaMain {
    public static final long starting_time = System.currentTimeMillis();

    public static void main(String[] args) {
        // the time to first print is quite long, if we wanted, we could start the compilation in a thread
        // and just print the "normal" stuff for the first few seconds while waiting for the compile to complete in the thread
        // it would have to have some blocking methods before it would be allowed to call into the runtime

        if("true".equals(System.getProperty("dyna.unchecked_math"))) {
            ((Var)Clojure.var("clojure.core", "*unchecked-math*")).bindRoot(true);
        }

        Clojure.var("clojure.core", "load").invoke("/dyna_backend/core"); // load and compile all of the files
        IFn main_function = Clojure.var("dyna-backend.core", "main"); // invoke the main method with the arguments now
        main_function.invoke(args);
    }
}
