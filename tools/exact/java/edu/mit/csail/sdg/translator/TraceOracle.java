package edu.mit.csail.sdg.translator;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.satlab.SATSolver;
import kodkod.solvers.SAT4JRef;

/**
 * Ground truth for the exact (Java-identical) pipeline.
 *
 * trace MODEL IDX OUTPREFIX : runs command IDX like AlloyOracle (sat4j, symmetry 20) through a SAT4J wrapper that
 * records every addVariables/addClause call, writes OUTPREFIX.cnf (one block per solver instance: "v n", clause
 * lines "c l1 l2 ..", "s SAT|UNSAT", "m 0101.." = model of vars 1..n) and OUTPREFIX.json (the Alloy instance).
 *
 * replay FILE.cnf : feeds each recorded block into a fresh SAT4J default solver, checks result + model.
 */
public class TraceOracle {

    static final List<StringBuilder> blocks = new ArrayList<>();

    static final class TraceSolver implements SATSolver {
        final SATSolver inner;
        final StringBuilder sb = new StringBuilder();
        int vars = 0;

        TraceSolver(SATSolver inner) {
            this.inner = inner;
            synchronized (blocks) {
                blocks.add(sb);
            }
        }
        public int numberOfVariables() { return inner.numberOfVariables(); }
        public int numberOfClauses() { return inner.numberOfClauses(); }
        public void addVariables(int n) {
            sb.append("v ").append(n).append('\n');
            vars += n;
            inner.addVariables(n);
        }
        public boolean addClause(int[] lits) {
            sb.append('c');
            for (int l : lits)
                sb.append(' ').append(l);
            sb.append('\n');
            return inner.addClause(lits);
        }
        public boolean solve() {
            boolean r = inner.solve();
            sb.append("s ").append(r ? "SAT" : "UNSAT").append('\n');
            if (r) {
                sb.append("m ");
                for (int i = 1; i <= vars; i++)
                    sb.append(inner.valueOf(i) ? '1' : '0');
                sb.append('\n');
            }
            return r;
        }
        public boolean valueOf(int v) { return inner.valueOf(v); }
        public void free() { inner.free(); }
    }

    static final class TraceFactory extends SATFactory {
        private static final long serialVersionUID = 1L;
        public String id() { return "sat4j"; }
        public boolean incremental() { return true; }
        public String type() { return "java"; }
        protected SATSolver createSolver() { return new TraceSolver(SAT4JRef.INSTANCE.instance()); }
    }

    public static void main(String[] args) throws Exception {
        PrintStream out = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
        System.setOut(new PrintStream(OutputStream.nullOutputStream()));
        System.setErr(new PrintStream(OutputStream.nullOutputStream()));
        try {
            if (args[0].equals("trace"))
                trace(out, args[1], Integer.parseInt(args[2]), args[3]);
            else if (args[0].equals("replay"))
                replay(out, args[1]);
        } catch (Throwable e) {
            Throwable c = e;
            while (c.getCause() != null)
                c = c.getCause();
            out.println("ERROR " + c);
            for (StackTraceElement el : c.getStackTrace())
                out.println("\tat " + el);
        }
        out.flush();
        System.exit(0);
    }

    static void trace(PrintStream out, String file, int idx, String prefix) throws Exception {
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, file);
        Command cmd = world.getAllCommands().get(idx);
        A4Options opt = new A4Options();
        opt.solver = new TraceFactory();
        opt.originalFilename = file;
        A4Solution sol = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, world.getAllReachableSigs(), cmd, opt);
        try (Writer w = new OutputStreamWriter(new FileOutputStream(prefix + ".cnf"), StandardCharsets.UTF_8)) {
            for (StringBuilder b : blocks) {
                w.write("begin\n");
                w.write(b.toString());
                w.write("end\n");
            }
        }
        String inst = sol.satisfiable() ? instanceJson(sol) : "null";
        Files.write(Paths.get(prefix + ".json"), inst.getBytes(StandardCharsets.UTF_8));
        out.println("OK " + (sol.satisfiable() ? "SAT" : "UNSAT") + " blocks=" + blocks.size());
    }

    static void replay(PrintStream out, String cnf) throws Exception {
        int bi = 0, ok = 0, bad = 0;
        org.sat4j.specs.ISolver s = null;
        int vars = 0;
        boolean contra = false;
        Boolean res = null;
        try (BufferedReader r = Files.newBufferedReader(Paths.get(cnf), StandardCharsets.UTF_8)) {
            String line;
            while ((line = r.readLine()) != null) {
                if (line.equals("begin")) {
                    s = org.sat4j.minisat.SolverFactory.newDefault();
                    vars = 0;
                    contra = false;
                    res = null;
                } else if (line.startsWith("v ")) {
                    int n = Integer.parseInt(line.substring(2));
                    if (n > 0) {
                        vars += n;
                        s.newVar(vars);
                    }
                } else if (line.startsWith("c")) {
                    if (contra)
                        continue;
                    String[] p = line.length() > 1 ? line.substring(2).split(" ") : new String[0];
                    int[] lits = new int[p.length];
                    for (int i = 0; i < p.length; i++)
                        lits[i] = Integer.parseInt(p[i]);
                    try {
                        s.addClause(new org.sat4j.core.VecInt(lits));
                    } catch (org.sat4j.specs.ContradictionException e) {
                        contra = true;
                    }
                } else if (line.startsWith("s ")) {
                    res = contra ? false : s.isSatisfiable();
                    boolean want = line.equals("s SAT");
                    if (res != want) {
                        out.println("block " + bi + ": result " + res + " != recorded " + want);
                        bad++;
                    }
                } else if (line.startsWith("m ")) {
                    String m = line.substring(2);
                    int diff = 0;
                    for (int i = 1; i <= vars && res != null && res; i++)
                        if ((s.model(i) ? '1' : '0') != m.charAt(i - 1))
                            diff++;
                    if (diff == 0)
                        ok++;
                    else {
                        bad++;
                        out.println("block " + bi + ": model differs in " + diff + " vars");
                    }
                } else if (line.equals("end")) {
                    bi++;
                }
            }
        }
        out.println("REPLAY blocks=" + bi + " model_ok=" + ok + " bad=" + bad);
    }

    static String instanceJson(A4Solution sol) throws Exception {
        boolean temporal = sol.getMinTrace() != -1;
        int len = temporal ? sol.getTraceLength() : 1;
        StringBuilder sb = new StringBuilder("{\"trace_length\":" + len + ",\"loop\":" + (temporal ? sol.getLoopState() : -1) + ",\"states\":[");
        for (int st = 0; st < len; st++) {
            if (st > 0)
                sb.append(',');
            TreeMap<String,List<String>> rels = new TreeMap<>();
            for (Sig s : sol.getAllReachableSigs()) {
                if (s.builtin)
                    continue;
                rels.put(s.label, PinCheck.tuples(temporal ? sol.eval(s, st) : sol.eval(s)));
                for (Sig.Field fld : s.getFields())
                    rels.put(s.label + "." + fld.label, PinCheck.tuples(temporal ? sol.eval(fld, st) : sol.eval(fld)));
            }
            for (ExprVar sk : sol.getAllSkolems()) {
                try {
                    Object v = temporal ? sol.eval(sk, st) : sol.eval(sk);
                    if (v instanceof A4TupleSet)
                        rels.put("skolem:" + sk.label, PinCheck.tuples((A4TupleSet) v));
                } catch (Throwable ignore) {}
            }
            sb.append('{');
            boolean first = true;
            for (Map.Entry<String,List<String>> e : rels.entrySet()) {
                if (!first)
                    sb.append(',');
                first = false;
                sb.append(PinCheck.q(e.getKey())).append(":[").append(String.join(",", e.getValue())).append(']');
            }
            sb.append('}');
        }
        return sb.append("]}").toString();
    }
}
