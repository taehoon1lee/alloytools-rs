package edu.mit.csail.sdg.translator;

import java.io.*;
import java.lang.reflect.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import kodkod.ast.Relation;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.*;

/**
 * Validates an externally produced (Rust) static instance with Java Alloy's own translation: every Kodkod relation
 * of Java's bounds that the instance names is bounded exactly to the instance's tuples (BookExamples.trial style),
 * then Java solves. SAT => the instance is a model of Java's formula (facts + negated assertion) with only the
 * unpinned relations (skolems) free. Prints the Java-normalized instance (sol.eval of sigs/fields/skolems).
 *
 * Usage: PinCheck model.als commandIndex instance.txt   (instance.txt: "rel\tNAME" lines followed by "t\tA\tB.." lines)
 */
public class PinCheck {

    public static void main(String[] args) throws Exception {
        PrintStream out0 = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
        try { run(args); } catch (Throwable e) { Throwable c = e; while (c.getCause() != null) c = c.getCause(); out0.println("RESULT	EXC " + c); for (StackTraceElement el : c.getStackTrace()) { out0.println("	at " + el); } out0.flush(); System.exit(2); }
    }

    static void run(String[] args) throws Exception {
        PrintStream out = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
        System.setOut(new PrintStream(OutputStream.nullOutputStream()));
        System.setErr(new PrintStream(OutputStream.nullOutputStream()));
        String file = args[0];
        int idx = Integer.parseInt(args[1]);
        Map<String,List<List<String>>> inst = new LinkedHashMap<>();
        List<List<String>> cur = null;
        for (String line : Files.readAllLines(Paths.get(args[2]), StandardCharsets.UTF_8)) {
            String[] p = line.split("\t", -1);
            if (p[0].equals("rel")) {
                cur = new ArrayList<>();
                inst.put(p[1], cur);
            } else if (p[0].equals("t")) {
                cur.add(Arrays.asList(p).subList(1, p.length));
            }
        }
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, file);
        Command cmd = world.getAllCommands().get(idx);
        A4Options opt = new A4Options();
        opt.solver = SATFactory.get("sat4j");
        opt.originalFilename = file;

        Constructor<TranslateAlloyToKodkod> c = TranslateAlloyToKodkod.class.getDeclaredConstructor(A4Reporter.class, A4Options.class, Iterable.class, Command.class);
        c.setAccessible(true);
        TranslateAlloyToKodkod tr = c.newInstance(A4Reporter.NOP, opt, world.getAllReachableSigs(), cmd);
        Method mf = TranslateAlloyToKodkod.class.getDeclaredMethod("makeFacts", Expr.class);
        mf.setAccessible(true);
        mf.invoke(tr, cmd.formula);
        Field ff = TranslateAlloyToKodkod.class.getDeclaredField("frame");
        ff.setAccessible(true);
        A4Solution frame = (A4Solution) ff.get(tr);
        Field bf = A4Solution.class.getDeclaredField("bounds");
        bf.setAccessible(true);
        Bounds b = (Bounds) bf.get(frame);
        TupleFactory fac = frame.getFactory();

        // Rust-name -> Java relation: exact name, else a unique module-qualified relation with the same "/Suffix"
        // (Rust labels sigs of opened modules "this/X"; Java uses the module alias, e.g. "ord/X")
        Map<String,Relation> byName = new LinkedHashMap<>();
        Map<String,List<Relation>> bySuffix = new HashMap<>();
        for (Relation r : b.relations()) {
            byName.put(r.name(), r);
            int sl = r.name().indexOf('/');
            if (sl >= 0)
                bySuffix.computeIfAbsent(r.name().substring(sl), k -> new ArrayList<>()).add(r);
        }
        // Rust atom -> Java atom: exact, else unique universe atom ending with "/" + name (Java: "bool/True$0")
        Map<String,String> atomMap = new HashMap<>();
        Map<String,List<String>> atomSuffix = new HashMap<>();
        for (int i = 0; i < fac.universe().size(); i++) {
            String a = fac.universe().atom(i).toString();
            atomMap.put(a, a);
            int sl = a.lastIndexOf('/');
            if (sl >= 0)
                atomSuffix.computeIfAbsent(a.substring(sl + 1), k -> new ArrayList<>()).add(a);
        }
        List<String> renamedAtoms = new ArrayList<>();
        Map<Relation,String> pinnedBy = new LinkedHashMap<>();
        List<String> unpinned = new ArrayList<>(), oob = new ArrayList<>(), badAtom = new ArrayList<>(), symb = new ArrayList<>(),
                        extra = new ArrayList<>(), mapped = new ArrayList<>(), stripped = new ArrayList<>();
        for (Map.Entry<String,List<List<String>>> e : inst.entrySet()) {
            String n = e.getKey();
            Relation r = byName.get(n);
            if (r == null && n.startsWith("this/")) {
                List<Relation> c2 = bySuffix.getOrDefault(n.substring(4), Collections.emptyList());
                List<Relation> free = new ArrayList<>();
                for (Relation x : c2)
                    if (!x.name().startsWith("this/") && !pinnedBy.containsKey(x))
                        free.add(x);
                if (free.size() == 1) {
                    r = free.get(0);
                    mapped.add(n + "->" + r.name());
                } else if (free.size() > 1) {
                    extra.add(n + "(ambiguous:" + free + ")");
                    continue;
                }
            }
            if (r == null) {
                extra.add(n);
                continue;
            }
            TupleSet lo = b.lowerBound(r), hi = b.upperBound(r);
            TupleSet set = fac.noneOf(r.arity());
            try {
                for (List<String> t0 : e.getValue()) {
                    List<Object> t = new ArrayList<>();
                    for (String a : t0) {
                        String ja = atomMap.get(a);
                        if (ja == null) {
                            List<String> c3 = atomSuffix.getOrDefault(a, Collections.emptyList());
                            if (c3.size() != 1)
                                throw new IllegalArgumentException("no unique atom for " + a);
                            ja = c3.get(0);
                            renamedAtoms.add(a + "->" + ja);
                        }
                        t.add(ja);
                    }
                    if (t.size() == r.arity() + 1) {
                        // Java: a field of a non-var "one sig" S is a2k(S) -> r (r without the first column)
                        stripped.add(n);
                        t = t.subList(1, t.size());
                    }
                    set.add(fac.tuple(t));
                }
            } catch (Throwable ex) {
                badAtom.add(n + ": " + ex.getMessage());
                continue;
            }
            if (lo == null || hi == null)
                symb.add(r.name());
            else if (!set.containsAll(lo) || !hi.containsAll(set)) {
                oob.add(r.name() + " java=[" + lo.size() + "," + hi.size() + "] rust=" + set.size() + (hi.size() < 20 ? " hi=" + hi + " rust=" + set : ""));
                continue;
            }
            b.boundExactly(r, set);
            pinnedBy.put(r, n);
        }
        for (Relation r : b.relations()) {
            if (pinnedBy.containsKey(r))
                continue;
            TupleSet lo = b.lowerBound(r), hi = b.upperBound(r);
            if (lo == null || hi == null)
                unpinned.add(r.name() + "(symbolic)");
            else if (!lo.equals(hi))
                unpinned.add(r.name());
        }
        out.println("PINNED\t" + String.join(",", pinnedBy.values()));
        out.println("MAPPED\t" + String.join(",", mapped));
        out.println("STRIPPED\t" + String.join(",", new TreeSet<>(stripped)));
        out.println("ATOMS\t" + String.join(",", new TreeSet<>(renamedAtoms)));
        out.println("UNPINNED\t" + String.join(",", unpinned));
        out.println("EXTRA\t" + String.join(",", extra));
        out.println("OOB\t" + String.join(" | ", oob));
        out.println("SYMB\t" + String.join(",", symb));
        out.println("BADATOM\t" + String.join(" | ", badAtom));
        A4Solution sol = frame.solve(A4Reporter.NOP, cmd, new Simplifier(), false);
        out.println("RESULT\t" + (sol.satisfiable() ? "SAT" : "UNSAT"));
        if (sol.satisfiable())
            out.println("INSTANCE\t" + instanceJson(sol));
        out.flush();
        System.exit(0);
    }

    // same normalization as harness/java-oracle AlloyOracle.instanceJson (static problems)
    static String instanceJson(A4Solution sol) throws Exception {
        TreeMap<String,List<String>> rels = new TreeMap<>();
        for (Sig s : sol.getAllReachableSigs()) {
            if (s.builtin)
                continue;
            rels.put(s.label, tuples(sol.eval(s)));
            for (Sig.Field fld : s.getFields())
                rels.put(s.label + "." + fld.label, tuples(sol.eval(fld)));
        }
        for (ExprVar sk : sol.getAllSkolems()) {
            try {
                Object v = sol.eval(sk);
                if (v instanceof A4TupleSet)
                    rels.put("skolem:" + sk.label, tuples((A4TupleSet) v));
            } catch (Throwable ignore) {}
        }
        StringBuilder sb = new StringBuilder("{\"trace_length\":1,\"loop\":-1,\"states\":[{");
        boolean first = true;
        for (Map.Entry<String,List<String>> e : rels.entrySet()) {
            if (!first)
                sb.append(',');
            first = false;
            sb.append(q(e.getKey())).append(":[").append(String.join(",", e.getValue())).append(']');
        }
        return sb.append("}]}").toString();
    }

    static List<String> tuples(A4TupleSet ts) {
        List<String> out = new ArrayList<>();
        for (A4Tuple t : ts) {
            StringBuilder sb = new StringBuilder("[");
            for (int i = 0; i < t.arity(); i++) {
                if (i > 0)
                    sb.append(',');
                sb.append(q(t.atom(i)));
            }
            out.add(sb.append(']').toString());
        }
        Collections.sort(out);
        return out;
    }

    static String q(String s) {
        StringBuilder sb = new StringBuilder("\"");
        for (char ch : s.toCharArray()) {
            if (ch == '"' || ch == '\\')
                sb.append('\\').append(ch);
            else if (ch < 0x20)
                sb.append(String.format("\\u%04x", (int) ch));
            else
                sb.append(ch);
        }
        return sb.append('"').toString();
    }
}
