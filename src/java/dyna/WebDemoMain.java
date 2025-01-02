package dyna;

import clojure.java.api.Clojure;
import clojure.lang.IFn;


/**
 * Main class for running in the web browser.  Will start the dyna runtime and
 * call the javascript to get the prompt from the user, and then return the resultb
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

    // public static void load() {
    //     RT.init();
    //     DynaMain.initRuntime();
    // }

    // public static String validate(String command) {
    //     try {
    //         Clojure.var("clojure.core", "read-string").invoke(command);
    //         return null;
    //     } catch(Exception err) {
    //         return err.toString();
    //     }
    // }

    // public static String run(String command) {
    //     IFn eval = Clojure.var("clojure.core", "eval");
    //     IFn read_string = Clojure.var("clojure.core", "read-string");
    //     Object result = eval.invoke(read_string.invoke(command));
    //     return result.toString();
    // }

}
