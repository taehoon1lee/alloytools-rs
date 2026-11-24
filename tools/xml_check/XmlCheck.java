import java.io.*;
import java.lang.reflect.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4viz.AlloyInstance;
import edu.mit.csail.sdg.alloy4viz.StaticInstanceReader;
import edu.mit.csail.sdg.alloy4viz.VizState;
import edu.mit.csail.sdg.ast.Assert;
import edu.mit.csail.sdg.ast.Command;
import edu.mit.csail.sdg.ast.Expr;
import edu.mit.csail.sdg.ast.Sig;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import edu.mit.csail.sdg.translator.A4Options;
import edu.mit.csail.sdg.translator.A4Solution;
import edu.mit.csail.sdg.translator.A4SolutionReader;
import edu.mit.csail.sdg.translator.A4Tuple;
import edu.mit.csail.sdg.translator.A4TupleSet;
import edu.mit.csail.sdg.translator.Simplifier;
import edu.mit.csail.sdg.translator.TranslateAlloyToKodkod;
import kodkod.ast.Relation;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;

public class XmlCheck {
    static final Map<String, CompModule> WORLD_CACHE = new HashMap<>();

    static CompModule loadWorld(String alsPath) throws Err {
        CompModule w = WORLD_CACHE.get(alsPath);
        if (w == null) {
            w = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, alsPath);
            WORLD_CACHE.put(alsPath, w);
        }
        return w;
    }

    static boolean isHigherOrder(Throwable t) {
        while (t != null) {
            if (t.getClass().getName().contains("HigherOrderDecl")) {
                return true;
            }
            if (t.getMessage() != null && t.getMessage().contains("higher-order")) {
                return true;
            }
            t = t.getCause();
        }
        return false;
    }

    static String q(String s) {
        if (s == null) return "null";
        StringBuilder sb = new StringBuilder(s.length() + 4);
        sb.append('"');
        for (int i = 0; i < s.length(); i++) {
            char c = s.charAt(i);
            switch (c) {
                case '"': sb.append("\\\""); break;
                case '\\': sb.append("\\\\"); break;
                case '\n': sb.append("\\n"); break;
                case '\r': sb.append("\\r"); break;
                case '\t': sb.append("\\t"); break;
                default:
                    if (c < 0x20) sb.append(String.format("\\u%04x", (int) c));
                    else sb.append(c);
            }
        }
        sb.append('"');
        return sb.toString();
    }

    static List<List<String>> evalTuples(A4Solution sol, Expr e) throws Err {
        Object res = sol.eval(e);
        if (!(res instanceof A4TupleSet)) {
            return Collections.emptyList();
        }
        A4TupleSet ts = (A4TupleSet) res;
        List<List<String>> out = new ArrayList<>();
        for (A4Tuple t : ts) {
            List<String> row = new ArrayList<>(t.arity());
            for (int i = 0; i < t.arity(); i++) {
                row.add(t.atom(i));
            }
            out.add(row);
        }
        return out;
    }

    static List<String> stripOneSig(List<String> t0, int arity) {
        if (t0.size() == arity + 1) {
            return t0.subList(1, t0.size());
        }
        return t0;
    }

    static void bindAtom(String ra, String ja, Map<String, String> rustToJava, Set<String> usedJava) {
        if (!rustToJava.containsKey(ra) && !usedJava.contains(ja)) {
            rustToJava.put(ra, ja);
            usedJava.add(ja);
        }
    }

    static boolean verifyHigherOrderByPinning(CompModule world, Command cmd, String alsFile, A4Solution xmlSol) throws Exception {
        Map<String, List<List<String>>> inst = new LinkedHashMap<>();
        for (Sig s : world.getAllReachableSigs()) {
            if (s.builtin) continue;
            inst.put(s.label, evalTuples(xmlSol, s));
            for (Sig.Field f : s.getFields()) {
                inst.put(s.label + "." + f.label, evalTuples(xmlSol, f));
            }
        }

        A4Options opt = new A4Options();
        opt.solver = SATFactory.get("sat4j");
        opt.originalFilename = alsFile;
        Constructor<TranslateAlloyToKodkod> ctor = TranslateAlloyToKodkod.class.getDeclaredConstructor(
            A4Reporter.class, A4Options.class, Iterable.class, Command.class);
        ctor.setAccessible(true);
        TranslateAlloyToKodkod tr = ctor.newInstance(A4Reporter.NOP, opt, world.getAllReachableSigs(), cmd);
        Method mf = TranslateAlloyToKodkod.class.getDeclaredMethod("makeFacts", Expr.class);
        mf.setAccessible(true);
        mf.invoke(tr, cmd.formula);
        Field ff = TranslateAlloyToKodkod.class.getDeclaredField("frame");
        ff.setAccessible(true);
        A4Solution frame = (A4Solution) ff.get(tr);
        Field bf = A4Solution.class.getDeclaredField("bounds");
        bf.setAccessible(true);
        Bounds b = (Bounds) bf.get(frame);
        TupleFactory fac = b.universe().factory();

        Map<String, Relation> byName = new LinkedHashMap<>();
        for (Relation r : b.relations()) {
            byName.put(r.name(), r);
        }
        // Derive <Parent>_remainder for non-abstract parent PrimSigs
        for (Sig s : world.getAllReachableSigs()) {
            if (s.builtin || !(s instanceof Sig.PrimSig)) continue;
            Sig.PrimSig ps = (Sig.PrimSig) s;
            SafeList<Sig.PrimSig> children = ps.children();
            if (children.isEmpty() || ps.isAbstract != null) continue;
            String remName = ps.label + "_remainder";
            if (!byName.containsKey(remName) || !inst.containsKey(ps.label)) continue;
            Set<String> childAtoms = new HashSet<>();
            for (Sig.PrimSig ch : children) {
                List<List<String>> ct = inst.get(ch.label);
                if (ct != null) for (List<String> t : ct) if (!t.isEmpty()) childAtoms.add(t.get(0));
            }
            List<List<String>> rem = new ArrayList<>();
            for (List<String> t : inst.get(ps.label)) {
                if (!t.isEmpty() && !childAtoms.contains(t.get(0))) rem.add(t);
            }
            inst.put(remName, rem);
        }

        Map<String, String> rustToJava = new HashMap<>();
        Set<String> usedJava = new HashSet<>();
        for (int i = 0; i < fac.universe().size(); i++) {
            String a = fac.universe().atom(i).toString();
            if (a.matches("-?\\d+") || a.startsWith("\"")) {
                bindAtom(a, a, rustToJava, usedJava);
            }
        }
        for (Map.Entry<String, List<List<String>>> e : inst.entrySet()) {
            Relation r = byName.get(e.getKey());
            if (r == null) continue;
            TupleSet lo = b.lowerBound(r), hi = b.upperBound(r);
            if (lo != null && hi != null && lo.equals(hi) && lo.size() == 1 && e.getValue().size() == 1) {
                List<String> rt = stripOneSig(e.getValue().get(0), r.arity());
                if (rt.size() == r.arity()) {
                    Tuple jt = lo.iterator().next();
                    for (int c = 0; c < r.arity(); c++) bindAtom(rt.get(c), jt.atom(c).toString(), rustToJava, usedJava);
                }
            }
        }
        for (Sig s : world.getAllReachableSigs()) {
            if (s.builtin || !(s instanceof Sig.PrimSig)) continue;
            Sig.PrimSig ps = (Sig.PrimSig) s;
            String rname = ps.children().isEmpty() ? ps.label : (ps.isAbstract == null ? ps.label + "_remainder" : null);
            if (rname == null) continue;
            Relation r = byName.get(rname);
            List<List<String>> tups = inst.get(rname);
            if (r == null || tups == null || b.upperBound(r) == null) continue;
            Set<String> hiAtoms = new LinkedHashSet<>();
            for (Tuple jt : b.upperBound(r)) hiAtoms.add(jt.atom(0).toString());
            for (List<String> t0 : tups) {
                if (t0.isEmpty()) continue;
                String ra = t0.get(0);
                if (!rustToJava.containsKey(ra) && hiAtoms.contains(ra) && !usedJava.contains(ra)) {
                    bindAtom(ra, ra, rustToJava, usedJava);
                }
            }
            for (List<String> t0 : tups) {
                if (t0.isEmpty()) continue;
                String ra = t0.get(0);
                if (rustToJava.containsKey(ra)) continue;
                for (String cand : hiAtoms) {
                    if (!usedJava.contains(cand)) {
                        bindAtom(ra, cand, rustToJava, usedJava);
                        break;
                    }
                }
            }
        }
        for (Relation r : new ArrayList<>(b.relations())) {
            List<List<String>> tups = inst.get(r.name());
            if (tups == null) continue;
            TupleSet lo = b.lowerBound(r), hi = b.upperBound(r);
            if (lo != null && hi != null && lo.equals(hi)) continue;
            TupleSet exact = fac.noneOf(r.arity());
            for (List<String> t0 : tups) {
                List<String> rt = stripOneSig(t0, r.arity());
                if (rt.size() != r.arity()) continue;
                String[] mapped = new String[r.arity()];
                boolean ok = true;
                for (int c = 0; c < r.arity(); c++) {
                    String ja = rustToJava.get(rt.get(c));
                    if (ja == null) {
                        ja = rt.get(c);
                        if (!fac.universe().contains(ja)) { ok = false; break; }
                    }
                    mapped[c] = ja;
                }
                if (ok) exact.add(fac.tuple((Object[]) mapped));
            }
            if (lo != null && !exact.containsAll(lo)) return false;
            if (hi != null && !hi.containsAll(exact)) return false;
            b.boundExactly(r, exact);
        }
        Method ms = A4Solution.class.getDeclaredMethod("solve", A4Reporter.class, Command.class, Simplifier.class, boolean.class);
        ms.setAccessible(true);
        A4Solution solved = (A4Solution) ms.invoke(frame, A4Reporter.NOP, cmd, new Simplifier(), false);
        return solved.satisfiable();
    }

    static Expr findAssertionExpr(CompModule world, Command cmd) {
        if (!cmd.check) return null;
        for (Assert a : world.getAllAssertions()) {
            if (a.label.equals(cmd.label)) {
                return a.expr;
            }
        }
        return null;
    }

    static String verifyOne(String alsPath, int cmdIdx, String tag, String xmlPath, boolean checkViz) {
        boolean readOk = false, vizOk = false, vizStateOk = !checkViz;
        boolean factsOk = false, cmdOk = false;
        Boolean assertViolated = null;
        String mode = "eval";
        String errMsg = null;

        try {
            CompModule world = loadWorld(alsPath);
            Command cmd = world.getAllCommands().get(cmdIdx);
            File xf = new File(xmlPath);
            A4Solution sol = A4SolutionReader.read(world.getAllReachableSigs(), new XMLNode(xf));
            readOk = sol != null && sol.satisfiable();
            if (!readOk) {
                return String.format(
                    "{\"tag\":%s,\"ok\":false,\"read_ok\":false,\"viz_ok\":false,\"viz_state_ok\":false,\"facts_ok\":false,\"cmd_ok\":false,\"assert_violated\":null,\"mode\":%s,\"error\":%s}",
                    q(tag), q(mode), q("A4SolutionReader returned null or unsatisfiable"));
            }

            int nStates = sol.getTraceLength();
            for (int st = 0; st < nStates; st++) {
                AlloyInstance ai = StaticInstanceReader.parseInstance(xf, st);
                if (checkViz) {
                    new VizState(ai);
                }
            }
            vizOk = true;
            if (checkViz) vizStateOk = true;

            try {
                Object fv = sol.eval(world.getAllReachableFacts());
                factsOk = Boolean.TRUE.equals(fv);
                Object cv = sol.eval(cmd.formula);
                cmdOk = Boolean.TRUE.equals(cv);
                if (cmd.check) {
                    Expr ae = findAssertionExpr(world, cmd);
                    if (ae != null) {
                        Object av = sol.eval(ae);
                        assertViolated = Boolean.FALSE.equals(av);
                    } else {
                        assertViolated = cmdOk;
                    }
                }
            } catch (Throwable ex) {
                if (isHigherOrder(ex)) {
                    mode = "higher_order_sat";
                    boolean sat = verifyHigherOrderByPinning(world, cmd, alsPath, sol);
                    factsOk = sat;
                    cmdOk = sat;
                    if (cmd.check) assertViolated = sat;
                    if (!sat) errMsg = "higher-order pinned SAT verification returned UNSAT";
                } else {
                    throw ex;
                }
            }
        } catch (Throwable t) {
            errMsg = t.toString();
        }

        boolean ok = readOk && vizOk && (!checkViz || vizStateOk) && factsOk && cmdOk
            && (assertViolated == null || assertViolated.booleanValue()) && errMsg == null;
        return String.format(
            "{\"tag\":%s,\"ok\":%s,\"read_ok\":%s,\"viz_ok\":%s,\"viz_state_ok\":%s,\"facts_ok\":%s,\"cmd_ok\":%s,\"assert_violated\":%s,\"mode\":%s,\"error\":%s}",
            q(tag), ok, readOk, vizOk, vizStateOk, factsOk, cmdOk,
            assertViolated == null ? "null" : assertViolated.toString(), q(mode), q(errMsg));
    }

    public static void main(String[] args) throws Exception {
        PrintStream realOut = new PrintStream(new FileOutputStream(FileDescriptor.out), true, StandardCharsets.UTF_8);
        System.setOut(new PrintStream(OutputStream.nullOutputStream()));
        System.setErr(new PrintStream(OutputStream.nullOutputStream()));

        if (args.length >= 1 && "--batch".equals(args[0])) {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
            String line;
            while ((line = br.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                String[] p = line.split("\t", -1);
                String als = p[0];
                int idx = Integer.parseInt(p[1]);
                String tag = p[2];
                String xml = p[3];
                boolean viz = p.length >= 5 && "1".equals(p[4]);
                realOut.println(verifyOne(als, idx, tag, xml, viz));
            }
            return;
        }
        if (args.length >= 1 && "--dump-java-xml".equals(args[0])) {
            BufferedReader br = new BufferedReader(new InputStreamReader(System.in, StandardCharsets.UTF_8));
            String line;
            while ((line = br.readLine()) != null) {
                if (line.trim().isEmpty()) continue;
                String[] p = line.split("\t", -1);
                String als = p[0];
                int idx = Integer.parseInt(p[1]);
                String tag = p[2];
                String outXml = p[3];
                try {
                    CompModule w = loadWorld(als);
                    Command c = w.getAllCommands().get(idx);
                    A4Options opt = new A4Options();
                    opt.solver = SATFactory.get("sat4j");
                    opt.originalFilename = als;
                    A4Solution sol = TranslateAlloyToKodkod.execute_command(A4Reporter.NOP, w.getAllReachableSigs(), c, opt);
                    File f = new File(outXml);
                    if (f.getParentFile() != null) f.getParentFile().mkdirs();
                    sol.writeXML(outXml, Collections.emptyList(), null);
                    realOut.println("{\"tag\":" + q(tag) + ",\"ok\":true}");
                } catch (Throwable t) {
                    realOut.println("{\"tag\":" + q(tag) + ",\"ok\":false,\"error\":" + q(t.toString()) + "}");
                }
            }
            return;
        }
        if (args.length >= 3) {
            boolean viz = args.length >= 4 && "--viz".equals(args[3]);
            String res = verifyOne(args[0], Integer.parseInt(args[1]), args[2], args[2], viz);
            realOut.println(res);
            if (!res.contains("\"ok\":true")) System.exit(1);
            return;
        }
        System.exit(2);
    }
}
