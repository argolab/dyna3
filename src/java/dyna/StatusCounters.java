package dyna;

public class StatusCounters {
    static private long rewrites_performed = 0;
    static private long matches_attempted = 0;
    static private long matches_successful = 0;
    static private long rexprs_created = 0;
    //static private long primitive_builtin_evaluated = 0;
    static private long jit_rewrites_performed = 0;

    static private long program_start_time = 0;
    static private long agenda_work_processed = 0;
    static private long agenda_time_processing = 0;

    private StatusCounters() {}

    public static void print_counters() {
        String p = "----------------------------------------------------\n" +
            "Rewrites performed: " + (rewrites_performed+jit_rewrites_performed) + "\n";
        if(jit_rewrites_performed != 0) {
            p += "JIT generated rewrites performed: " + jit_rewrites_performed + " ("+String.format("%.2f", ((double)jit_rewrites_performed*100)/(rewrites_performed+jit_rewrites_performed))+"%)\n";
        }
        p += "Matches attempted: " + matches_attempted + "\n" +
            "Matches successful: " + (matches_successful+jit_rewrites_performed) + "\n" +
            "Rexprs created: " + rexprs_created + "\n";
        if(program_start_time != 0) {
            String runtime = String.format("%.2f", (System.currentTimeMillis() - program_start_time) / 1000.0);
            p += "Program run time: " + runtime + " (secs) \n";
        }
        System.out.print(p);
    }

    public static void rewrite_performed() { rewrites_performed++; }
    public static void match_attempt() { matches_attempted++; }
    public static void match_sucessful() { matches_successful++; }
    public static void rexpr_created() { rexprs_created++; }
    public static void program_start() { program_start_time = System.currentTimeMillis(); }
    public static void jit_rewrite_performed() { jit_rewrites_performed++; }

    public static void agenda_processing_time(long work, long time) {
        agenda_work_processed += work;
        agenda_time_processing += time;
    }

    public static final boolean run_counters = Boolean.parseBoolean(System.getProperty("dyna.status_counters", "true"));
}
