package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;


/**
 * Main class for running in the web browser.  Will start the dyna runtime and receive
 * calls from javascript that manages the prompt from the user.
 */
public class WebDemoMain {

    private static IFn run_command;
    private static IFn validate_command;

    public static void load() {
        DynaMain.initRuntime();
        run_command = (IFn)Clojure.var("dyna.repl", "web-repl-run-command");
        validate_command = (IFn)Clojure.var("dyna.repl", "web-repl-validate-command");
    }

    public static String validate(String command) {
        return (String)validate_command.invoke(command);
    }

    public static String run(String command) {
        return (String)run_command.invoke(command);
    }

}
