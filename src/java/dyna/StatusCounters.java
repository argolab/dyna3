package dyna;

public class StatusCounters {
    static private long rewrites_performed = 0;
    static private long matches_attempted = 0;
    static private long matches_successful = 0;
    static private long rexprs_created = 0;
    static private long primitive_builtin_evaluated = 0;

    static private long program_start_time = 0;

    private StatusCounters() {}

    public static void print_counters() {
        System.out.print("------------------------------\n" +
                         "Rewrites performed: " + rewrites_performed + "\n" +
                         "Matches attempted: " + matches_attempted + "\n" +
                         "Matches successful: " + matches_successful + "\n" +
                         "Rexprs created: " + rexprs_created + "\n");
        if(program_start_time != 0) {
            String runtime = String.format("%.2f", (System.currentTimeMillis() - program_start_time) / 1000.0);
            System.out.print("Program run time: " + runtime + " (secs) \n");
        }
    }

    public static void rewrite_performed() { rewrites_performed++; }
    public static void match_attempt() { matches_attempted++; }
    public static void match_sucessful() { matches_successful++; }
    public static void rexpr_created() { rexprs_created++; }
    public static void program_start() { program_start_time = System.currentTimeMillis(); }
}
