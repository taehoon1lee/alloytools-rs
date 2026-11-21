import java.io.File;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorType;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.ExprVar;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.engine.satlab.SATFactory;

/**
 * Golden-output oracle for the Rust rewrite.
 *
 * Runs every command of one .als file with the official Java Alloy API and
 * prints ONE normalized JSON document (see harness/SCHEMA.md) on stdout. The
 * Rust CLI (`alloy-rs exec --json`) must print the same schema.
 *
 * Usage: java -cp alloy.jar;oracle AlloyOracle --file F [--display-name N]
 *        [--timeout-ms MS] [--start I] [--count N] [--symmetry S]
 *        [--solver sat4j] [--no-instance]
 *
 * If a command exceeds --timeout-ms, it is reported as TIMEOUT, the JSON is
 * printed and the JVM exits with code 3 (the stuck solver thread cannot be
 * killed). The caller then restarts with --start index+1 and merges results.
 */
public class AlloyOracle {

    static String  file;
    static String  displayName;
    static long    timeoutMs  = 60000;
    static int     start      = 0;
    static int     count      = 0;
    static int     symmetry   = 20;
    static String  solverId   = "sat4j";
    static boolean instance   = true;

    public static void main(String[] args) throws Exception {
        for (int i = 0; i < args.length; i++) {
            switch (args[i]) {
                case "--file" :         file = args[++i]; break;
                case "--display-name" : displayName = args[++i]; break;
                case "--timeout-ms" :   timeoutMs = Long.parseLong(args[++i]); break;
                case "--start" :        start = Integer.parseInt(args[++i]); break;
                case "--count" :        count = Integer.parseInt(args[++i]); break;
                case "--symmetry" :     symmetry = Integer.parseInt(args[++i]); break;
                case "--solver" :       solverId = args[++i]; break;
                case "--no-instance" :  instance = false; break;
                default :
                    System.err.println("unknown arg " + args[i]);
                    System.exit(2);
            }
        }
        if (displayName == null)
            displayName = file;
        // keep stdout clean: Alloy/Kodkod/SAT4J sometimes print to System.out
        PrintStream realOut = new PrintStream(new java.io.FileOutputStream(java.io.FileDescriptor.out), true, StandardCharsets.UTF_8);
        System.setOut(System.err);

        Json out = new Json();
        out.begin();
        out.field("schema", 1);
        out.field("tool", "java-alloy-6.2.0");
        out.field("file", displayName);
        out.field("start", start);

        A4Reporter rep = new A4Reporter();
        CompModule world;
        long p0 = System.nanoTime();
        try {
            world = CompUtil.parseEverything_fromFile(rep, new HashMap<String,String>(), file);
        } catch (Err e) {
            double parseMs = ms(p0);
            String kind = e instanceof ErrorSyntax ? "syntax_error" : e instanceof ErrorType ? "type_error" : "error";
            out.field("status", kind);
            out.key("error");
            errObj(out, kind, e);
            out.field("parse_ms", parseMs);
            out.key("commands");
            out.raw("[]");
            out.end();
            realOut.println(out);
            System.exit(0);
            return;
        } catch (Throwable t) {
            out.field("status", "error");
            out.key("error");
            out.begin();
            out.field("kind", "crash");
            out.field("msg", String.valueOf(t));
            out.end();
            out.key("commands");
            out.raw("[]");
            out.end();
            realOut.println(out);
            System.exit(0);
            return;
        }
        double parseMs = ms(p0);
        out.field("status", "ok");
        out.key("error");
        out.raw("null");
        out.field("parse_ms", parseMs);

        List<Command> cmds = world.getAllCommands();
        out.field("command_count", cmds.size());
        out.key("commands");
        out.raw("[");
        ExecutorService ex = Executors.newSingleThreadExecutor(r -> {
            Thread t = new Thread(null, r, "solve", 256L * 1024 * 1024);
            t.setDaemon(true);
            return t;
        });
        boolean first = true;
        int exitCode = 0;
        for (int i = start; i < cmds.size(); i++) {
            final Command cmd = cmds.get(i);
            final int idx = i;
            Future<String> f = ex.submit(() -> runCommand(world, cmd, idx));
            String res;
            try {
                res = f.get(timeoutMs, TimeUnit.MILLISECONDS);
            } catch (TimeoutException te) {
                Json j = cmdHeader(cmd, idx);
                j.field("status", "TIMEOUT");
                j.field("timeout_ms", timeoutMs);
                j.end();
                res = j.toString();
                exitCode = 3;
            }
            if (!first)
                out.raw(",");
            first = false;
            out.raw(res);
            if (exitCode != 0)
                break;
        }
        out.raw("]");
        out.end();
        realOut.println(out);
        realOut.flush();
        System.exit(exitCode);
    }

    static Json cmdHeader(Command cmd, int idx) {
        Json j = new Json();
        j.begin();
        j.field("index", idx);
        j.field("label", cmd.label);
        j.field("kind", cmd.check ? "check" : "run");
        j.field("expects", cmd.expects);
        j.field("scope", cmd.toString());
        j.field("overall", cmd.overall);
        j.field("bitwidth", cmd.bitwidth);
        j.field("maxseq", cmd.maxseq);
        j.field("minprefix", cmd.minprefix);
        j.field("maxprefix", cmd.maxprefix);
        return j;
    }

    static String runCommand(CompModule world, Command cmd, int idx) {
        Json j = cmdHeader(cmd, idx);
        A4Options opt = new A4Options();
        opt.solver = SATFactory.get(solverId);
        opt.symmetry = symmetry;
        opt.originalFilename = file;
        final long[] tSolve = new long[] {
                                          0
        };
        final int[] stats = new int[] {
                                       -1, -1, -1
        };
        A4Reporter rep = new A4Reporter() {

            @Override
            public void solve(int plength, int primaryVars, int totalVars, int clauses) {
                tSolve[0] = System.nanoTime();
                stats[0] = primaryVars;
                stats[1] = totalVars;
                stats[2] = clauses;
            }
        };
        long t0 = System.nanoTime();
        try {
            A4Solution sol = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), cmd, opt);
            long t1 = System.nanoTime();
            boolean sat = sol.satisfiable();
            j.field("status", sat ? "SAT" : "UNSAT");
            j.key("error");
            j.raw("null");
            // mintrace == -1 means a static (non-temporal) problem
            j.field("temporal", sol.getMinTrace() != -1);
            j.field("min_trace", sol.getMinTrace());
            j.field("max_trace", sol.getMaxTrace());
            long ts = tSolve[0] == 0 ? t1 : tSolve[0];
            j.field("translate_ms", (ts - t0) / 1e6);
            j.field("solve_ms", (t1 - ts) / 1e6);
            j.field("total_ms", (t1 - t0) / 1e6);
            j.key("stats");
            j.begin();
            j.field("primary_vars", stats[0]);
            j.field("vars", stats[1]);
            j.field("clauses", stats[2]);
            j.end();
            if (sat && instance) {
                j.key("instance");
                instanceJson(j, sol);
            }
            if (count > 0) {
                long c0 = System.nanoTime();
                int n = 0;
                A4Solution s = sol;
                while (s.satisfiable() && n < count) {
                    n++;
                    s = s.next();
                }
                j.field("count", n);
                j.field("count_capped", n >= count && s.satisfiable());
                j.field("count_ms", ms(c0));
            }
        } catch (Err e) {
            j.field("status", "ERROR");
            j.key("error");
            errObj(j, e instanceof ErrorType ? "type_error" : "error", e);
            j.field("total_ms", ms(t0));
        } catch (Throwable e) {
            j.field("status", "ERROR");
            j.key("error");
            j.begin();
            j.field("kind", "crash");
            j.field("msg", String.valueOf(e));
            j.end();
            j.field("total_ms", ms(t0));
        }
        j.end();
        return j.toString();
    }

    /** {"trace_length":n,"loop":k,"states":[{"rel":[["a","b"],...]}, ...]} with sorted keys/tuples */
    static void instanceJson(Json j, A4Solution sol) throws Err {
        boolean temporal = sol.getMinTrace() != -1;
        int len = temporal ? sol.getTraceLength() : 1;
        j.begin();
        j.field("trace_length", len);
        j.field("loop", temporal ? sol.getLoopState() : -1);
        j.key("states");
        j.raw("[");
        for (int st = 0; st < len; st++) {
            if (st > 0)
                j.raw(",");
            TreeMap<String,List<String>> rels = new TreeMap<>();
            for (Sig s : sol.getAllReachableSigs()) {
                if (s.builtin)
                    continue;
                rels.put(s.label, tuples(temporal ? sol.eval(s, st) : sol.eval(s)));
                for (Sig.Field fld : s.getFields()) {
                    rels.put(s.label + "." + fld.label, tuples(temporal ? sol.eval(fld, st) : sol.eval(fld)));
                }
            }
            for (ExprVar sk : sol.getAllSkolems()) {
                try {
                    Object v = temporal ? sol.eval(sk, st) : sol.eval(sk);
                    if (v instanceof A4TupleSet)
                        rels.put("skolem:" + sk.label, tuples((A4TupleSet) v));
                } catch (Throwable ignore) {}
            }
            j.begin();
            for (Map.Entry<String,List<String>> e : rels.entrySet()) {
                j.key(e.getKey());
                j.raw("[" + String.join(",", e.getValue()) + "]");
            }
            j.end();
        }
        j.raw("]");
        j.end();
    }

    static List<String> tuples(A4TupleSet ts) {
        List<String> out = new ArrayList<>();
        for (A4Tuple t : ts) {
            StringBuilder sb = new StringBuilder("[");
            for (int i = 0; i < t.arity(); i++) {
                if (i > 0)
                    sb.append(',');
                sb.append(Json.quote(t.atom(i)));
            }
            sb.append(']');
            out.add(sb.toString());
        }
        java.util.Collections.sort(out);
        return out;
    }

    static void errObj(Json j, String kind, Err e) {
        j.begin();
        j.field("kind", kind);
        j.field("line", e.pos == null ? -1 : e.pos.y);
        j.field("col", e.pos == null ? -1 : e.pos.x);
        String fn = e.pos == null || e.pos.filename == null ? "" : new File(e.pos.filename).getName();
        j.field("in_file", fn);
        j.field("msg", e.msg == null ? "" : e.msg.trim());
        j.end();
    }

    static double ms(long t0) {
        return (System.nanoTime() - t0) / 1e6;
    }

    /** Tiny streaming JSON builder (no dependencies). */
    static final class Json {

        final StringBuilder sb    = new StringBuilder();
        // stack of "needs comma" flags
        final List<Boolean> comma = new ArrayList<>();

        void sep() {
            if (!comma.isEmpty()) {
                int k = comma.size() - 1;
                if (comma.get(k))
                    sb.append(',');
                comma.set(k, true);
            }
        }

        void begin() {
            sb.append('{');
            comma.add(false);
        }

        void end() {
            sb.append('}');
            comma.remove(comma.size() - 1);
        }

        void key(String k) {
            sep();
            sb.append(quote(k)).append(':');
        }

        void raw(String s) {
            sb.append(s);
        }

        void field(String k, String v) {
            key(k);
            sb.append(v == null ? "null" : quote(v));
        }

        void field(String k, long v) {
            key(k);
            sb.append(v);
        }

        void field(String k, double v) {
            key(k);
            sb.append(String.format(java.util.Locale.ROOT, "%.3f", v));
        }

        void field(String k, boolean v) {
            key(k);
            sb.append(v);
        }

        static String quote(String s) {
            StringBuilder b = new StringBuilder("\"");
            for (char c : s.toCharArray()) {
                switch (c) {
                    case '"' :
                        b.append("\\\"");
                        break;
                    case '\\' :
                        b.append("\\\\");
                        break;
                    case '\n' :
                        b.append("\\n");
                        break;
                    case '\r' :
                        b.append("\\r");
                        break;
                    case '\t' :
                        b.append("\\t");
                        break;
                    default :
                        if (c < 0x20)
                            b.append(String.format("\\u%04x", (int) c));
                        else
                            b.append(c);
                }
            }
            return b.append('"').toString();
        }

        @Override
        public String toString() {
            return sb.toString();
        }
    }
}
