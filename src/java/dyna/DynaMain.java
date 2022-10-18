package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;
import clojure.lang.Var;

class DynaMain {
    public static final long starting_time = System.currentTimeMillis();
    private static boolean is_loading = false;
    private static final Object loading_lock = new Object();

    public static void main(String[] args) {
        // the time to first print is quite long, if we wanted, we could start the compilation in a thread
        // and just print the "normal" stuff for the first few seconds while waiting for the compile to complete in the thread
        // it would have to have some blocking methods before it would be allowed to call into the runtime

        is_loading = true;
        if(Boolean.getBoolean("dyna.loading_spin")) {
            System.out.print("\033[?25l"); // hide the cursor
            Thread t = new Thread(new Runnable () {
                    public void run() {
                        int step = 0;
                        while(is_loading) {
                            String s = "Loading... ";
                            switch(step++ %4) {
                            case 0: s += "/"; break;
                            case 1: s += "-"; break;
                            case 2: s += "\\"; break;
                            case 3: s += "|"; break;
                            }
                            System.out.print(s + "\r");
                            System.out.flush();
                            try {
                                Thread.sleep(90);
                            } catch(InterruptedException e) { break; }
                        }
                    }
                });
            t.setDaemon(true);
            t.start();
        }

        initRuntime(); // do the actual init of the runtime, this function takes a few seconds

        if(Boolean.getBoolean("dyna.loading_spin")) {
            // show the cursor again and clear the line
            System.out.print("\033[?25h\r\033[K");
        }

        IFn main_function = Clojure.var("dyna.core", "main"); // invoke the main method with the arguments now
        main_function.invoke(args);
    }

    public static void initRuntime() {
        // anything about setting up the clojure runtime before we begin or loading the files should be done here
        // then we can call this from other places which might serve as entry points to the runtime
        synchronized (loading_lock) {
            is_loading = true;
            if("true".equals(System.getProperty("dyna.unchecked_math"))) {
                ((Var)Clojure.var("clojure.core", "*unchecked-math*")).bindRoot(true);
            }

            Clojure.var("clojure.core", "load").invoke("/dyna/core"); // load all of the files
            is_loading = false;
        }
    }

    public static void backgroundInit() {
        // the runtime takes a few seconds to load.  So from the Python wrapper,
        // we can start that loading in the background without blocking the main
        // python thread
        Thread t = new Thread(new Runnable () {
                public void run() {
                    initRuntime();
                }
            });
        t.start();
    }
}
