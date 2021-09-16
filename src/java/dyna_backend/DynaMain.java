package dyna_backend;

import clojure.java.api.Clojure;
import clojure.lang.IFn;

class DynaMain {
    public static void main(String[] args) {
        // the time to first print is quite long, if we wanted, we could start the compilation in a thread
        // and just print the "normal" stuff for the first few seconds while waiting for the compile to complete in the thread
        // it would have to have some blocking methods before it would be allowed to call into the runtime

        Clojure.var("clojure.core", "load").invoke("/dyna_backend/core"); // load and compile all of the files
        IFn main_function = Clojure.var("dyna-backend.core", "main"); // invoke the main method with the arguments now
        main_function.invoke(args);
    }
}
