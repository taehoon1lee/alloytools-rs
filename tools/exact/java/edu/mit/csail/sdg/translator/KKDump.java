package edu.mit.csail.sdg.translator;

import java.io.*;
import java.lang.reflect.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.ast.*;
import edu.mit.csail.sdg.parser.CompModule;
import edu.mit.csail.sdg.parser.CompUtil;
import kodkod.ast.*;
import kodkod.engine.*;
import kodkod.engine.config.ExtendedOptions;
import kodkod.instance.*;

/**
 * Dumps the Kodkod problem (formula DAG + PardinusBounds + options) that Alloy hands to PardinusSolver.solveAll,
 * then lets the solve continue (with the TraceOracle SAT4J tracer) and writes the CNF trace + instance.
 *
 * usage: KKDump MODEL IDX OUTPREFIX   -> OUTPREFIX.kk, OUTPREFIX.cnf, OUTPREFIX.json
 *
 * .kk format (one item per line, ids are node ids, nodes are emitted before use):
 *   U n / A atom             universe
 *   O key=value ...          options
 *   n id KIND args...        node (see emit())
 *   R relid                  bounds.relations() order
 *   L relid idx..  / H relid idx..   concrete lower / upper (tuple indices)
 *   SB relid lowerExprId upperExprId  symbolic bounds, in insertion order
 *   IB int idx..             int bounds
 *   G formulaId              the goal
 */
public class KKDump {

    static final class Dumper {
        final StringBuilder sb = new StringBuilder();
        final IdentityHashMap<Object,Integer> ids = new IdentityHashMap<>();
        int next = 0;

        static String q(String s) {
            return PinCheck.q(s);
        }

        int id(Object n) {
            Integer i = ids.get(n);
            if (i != null)
                return i;
            String line = emit(n);
            int k = next++;
            ids.put(n, k);
            sb.append("n ").append(k).append(' ').append(line).append('\n');
            return k;
        }

        String ids(List< ? > xs) {
            StringBuilder b = new StringBuilder();
            for (Object x : xs)
                b.append(' ').append(id(x));
            return b.toString();
        }

        String emit(Object n) {
            if (n instanceof Relation) {
                Relation r = (Relation) n;
                return "REL " + r.arity() + " " + (r.isVariable() ? 1 : 0) + " " + (r.isAtom() ? 1 : 0) + " " + q(r.name());
            }
            if (n instanceof Variable) {
                Variable v = (Variable) n;
                return "VAR " + v.arity() + " " + q(v.name());
            }
            if (n instanceof ConstantExpression) {
                if (n == Expression.UNIV)
                    return "CONSTE UNIV";
                if (n == Expression.IDEN)
                    return "CONSTE IDEN";
                if (n == Expression.NONE)
                    return "CONSTE NONE";
                if (n == Expression.INTS)
                    return "CONSTE INTS";
                return "CONSTE ? " + n;
            }
            if (n instanceof ConstantFormula)
                return "CONSTF " + (((ConstantFormula) n).booleanValue() ? "TRUE" : "FALSE");
            if (n instanceof BinaryExpression) {
                BinaryExpression b = (BinaryExpression) n;
                int l = id(b.left()), r = id(b.right());
                return "BINE " + b.op().name() + " " + l + " " + r;
            }
            if (n instanceof UnaryExpression) {
                UnaryExpression u = (UnaryExpression) n;
                return "UNE " + u.op().name() + " " + id(u.expression());
            }
            if (n instanceof NaryExpression) {
                NaryExpression e = (NaryExpression) n;
                List<Object> cs = new ArrayList<>();
                for (int i = 0; i < e.size(); i++)
                    cs.add(e.child(i));
                return "NARYE " + e.op().name() + ids(cs);
            }
            if (n instanceof Comprehension) {
                Comprehension c = (Comprehension) n;
                int d = id(c.decls()), f = id(c.formula());
                return "COMPR " + d + " " + f;
            }
            if (n instanceof IfExpression) {
                IfExpression e = (IfExpression) n;
                int c = id(e.condition()), t = id(e.thenExpr()), el = id(e.elseExpr());
                return "IFE " + c + " " + t + " " + el;
            }
            if (n instanceof ProjectExpression) {
                ProjectExpression p = (ProjectExpression) n;
                StringBuilder b = new StringBuilder("PROJ " + id(p.expression()));
                for (int i = 0; i < p.arity(); i++)
                    b.append(' ').append(id(p.column(i)));
                return b.toString();
            }
            if (n instanceof IntToExprCast) {
                IntToExprCast c = (IntToExprCast) n;
                return "I2E " + c.op().name() + " " + id(c.intExpr());
            }
            if (n instanceof ExprToIntCast) {
                ExprToIntCast c = (ExprToIntCast) n;
                return "E2I " + c.op().name() + " " + id(c.expression());
            }
            if (n instanceof IntConstant)
                return "ICONST " + ((IntConstant) n).value();
            if (n instanceof BinaryIntExpression) {
                BinaryIntExpression b = (BinaryIntExpression) n;
                int l = id(b.left()), r = id(b.right());
                return "BINI " + b.op().name() + " " + l + " " + r;
            }
            if (n instanceof NaryIntExpression) {
                NaryIntExpression e = (NaryIntExpression) n;
                List<Object> cs = new ArrayList<>();
                for (int i = 0; i < e.size(); i++)
                    cs.add(e.child(i));
                return "NARYI " + e.op().name() + ids(cs);
            }
            if (n instanceof UnaryIntExpression) {
                UnaryIntExpression u = (UnaryIntExpression) n;
                return "UNI " + u.op().name() + " " + id(u.intExpr());
            }
            if (n instanceof SumExpression) {
                SumExpression s = (SumExpression) n;
                int d = id(s.decls()), e = id(s.intExpr());
                return "SUM " + d + " " + e;
            }
            if (n instanceof IfIntExpression) {
                IfIntExpression e = (IfIntExpression) n;
                int c = id(e.condition()), t = id(e.thenExpr()), el = id(e.elseExpr());
                return "IFI " + c + " " + t + " " + el;
            }
            if (n instanceof IntComparisonFormula) {
                IntComparisonFormula c = (IntComparisonFormula) n;
                int l = id(c.left()), r = id(c.right());
                return "ICMP " + c.op().name() + " " + l + " " + r;
            }
            if (n instanceof ComparisonFormula) {
                ComparisonFormula c = (ComparisonFormula) n;
                int l = id(c.left()), r = id(c.right());
                return "CMP " + c.op().name() + " " + l + " " + r;
            }
            if (n instanceof MultiplicityFormula) {
                MultiplicityFormula m = (MultiplicityFormula) n;
                return "MULT " + m.multiplicity().name() + " " + id(m.expression());
            }
            if (n instanceof QuantifiedFormula) {
                QuantifiedFormula f = (QuantifiedFormula) n;
                int d = id(f.decls()), b = id(f.formula());
                return "QUANT " + f.quantifier().name() + " " + d + " " + b;
            }
            if (n instanceof BinaryFormula) {
                BinaryFormula b = (BinaryFormula) n;
                int l = id(b.left()), r = id(b.right());
                return "BINF " + b.op().name() + " " + l + " " + r;
            }
            if (n instanceof NaryFormula) {
                NaryFormula f = (NaryFormula) n;
                List<Object> cs = new ArrayList<>();
                for (int i = 0; i < f.size(); i++)
                    cs.add(f.child(i));
                return "NARYF " + f.op().name() + ids(cs);
            }
            if (n instanceof NotFormula)
                return "NOT " + id(((NotFormula) n).formula());
            if (n instanceof RelationPredicate) {
                RelationPredicate p = (RelationPredicate) n;
                switch (p.name()) {
                    case ACYCLIC :
                        return "PACYCLIC " + id(p.relation());
                    case FUNCTION : {
                        RelationPredicate.Function f = (RelationPredicate.Function) p;
                        int r = id(f.relation()), d = id(f.domain()), rg = id(f.range());
                        return "PFUNCTION " + r + " " + d + " " + f.targetMult().name() + " " + rg;
                    }
                    case TOTAL_ORDERING : {
                        RelationPredicate.TotalOrdering t = (RelationPredicate.TotalOrdering) p;
                        int r = id(t.relation()), o = id(t.ordered()), fi = id(t.first()), la = id(t.last());
                        return "PTOTAL " + r + " " + o + " " + fi + " " + la;
                    }
                }
            }
            if (n instanceof kodkod.ast.Decl) {
                kodkod.ast.Decl d = (kodkod.ast.Decl) n;
                int v = id(d.variable()), e = id(d.expression());
                return "DECL " + v + " " + d.multiplicity().name() + " " + e;
            }
            if (n instanceof Decls) {
                Decls ds = (Decls) n;
                List<Object> cs = new ArrayList<>();
                for (int i = 0; i < ds.size(); i++)
                    cs.add(ds.get(i));
                return "DECLS" + ids(cs);
            }
            if (n instanceof UnaryTempFormula) {
                UnaryTempFormula u = (UnaryTempFormula) n;
                return "UTEMPF " + u.op().name() + " " + id(u.formula());
            }
            if (n instanceof BinaryTempFormula) {
                BinaryTempFormula b = (BinaryTempFormula) n;
                int l = id(b.left()), r = id(b.right());
                return "BTEMPF " + b.op().name() + " " + l + " " + r;
            }
            if (n instanceof TempExpression) {
                TempExpression t = (TempExpression) n;
                return "TEMPE " + t.op().name() + " " + id(t.expression());
            }
            throw new IllegalArgumentException("unknown node " + n.getClass());
        }

        static String idx(TupleSet ts) {
            StringBuilder b = new StringBuilder();
            for (Tuple t : ts)
                b.append(' ').append(t.index());
            return b.toString();
        }

        void dump(Formula goal, PardinusBounds b, ExtendedOptions o) {
            Universe u = b.universe();
            StringBuilder head = new StringBuilder();
            head.append("U ").append(u.size()).append('\n');
            for (int i = 0; i < u.size(); i++)
                head.append("A ").append(q(u.atom(i).toString())).append('\n');
            head.append("O bitwidth=").append(o.bitwidth()).append(" symmetry=").append(o.symmetryBreaking()).append(" skolemDepth=").append(o.skolemDepth()).append(" sharing=").append(o.sharing()).append(" noOverflow=").append(o.noOverflow()).append(" intEncoding=").append(o.intEncoding()).append(" temporal=").append(o.temporal()).append(" minTrace=").append(o.minTraceLength()).append(" maxTrace=").append(o.maxTraceLength()).append(" coreGranularity=").append(o.coreGranularity()).append(" logTranslation=").append(o.logTranslation()).append(" decomposed=").append(o.decomposed()).append('\n');
            int g = id(goal);
            StringBuilder tail = new StringBuilder();
            for (Relation r : b.relations())
                tail.append("R ").append(id(r)).append('\n');
            for (Relation r : b.relations()) {
                TupleSet lo = b.lowerBound(r), hi = b.upperBound(r);
                if (lo != null)
                    tail.append("L ").append(id(r)).append(idx(lo)).append('\n');
                if (hi != null)
                    tail.append("H ").append(id(r)).append(idx(hi)).append('\n');
            }
            for (Map.Entry<Relation,Expression> e : b.lowerSymbBounds().entrySet()) {
                int r = id(e.getKey());
                int lo = id(e.getValue());
                int hi = id(b.upperSymbBound(e.getKey()));
                tail.append("SB ").append(r).append(' ').append(lo).append(' ').append(hi).append('\n');
            }
            // PardinusBounds.symbolic.compls: original relation -> its "_compl" stand-in
            try {
                Field sf = PardinusBounds.class.getDeclaredField("symbolic");
                sf.setAccessible(true);
                Object sym = sf.get(b);
                Field cf = sym.getClass().getDeclaredField("compls");
                cf.setAccessible(true);
                @SuppressWarnings("unchecked")
                Map<Relation,Relation> compls = (Map<Relation,Relation>) cf.get(sym);
                for (Map.Entry<Relation,Relation> e : compls.entrySet())
                    tail.append("SC ").append(id(e.getKey())).append(' ').append(id(e.getValue())).append('\n');
            } catch (ReflectiveOperationException ex) {
                throw new RuntimeException(ex);
            }
            for (kodkod.util.ints.IndexedEntry<TupleSet> e : b.intBounds())
                tail.append("IB ").append(e.index()).append(idx(e.value())).append('\n');
            tail.append("G ").append(g).append('\n');
            sb.insert(0, head);
            sb.append(tail);
        }
    }

    static String dumped = null;

    public static void main(String[] args) throws Exception {
        PrintStream out = new PrintStream(new FileOutputStream(FileDescriptor.out), true, "UTF-8");
        System.setOut(new PrintStream(OutputStream.nullOutputStream()));
        System.setErr(new PrintStream(OutputStream.nullOutputStream()));
        try {
            run(out, args[0], Integer.parseInt(args[1]), args[2]);
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

    static void run(PrintStream out, String file, int idx, String prefix) throws Exception {
        CompModule world = CompUtil.parseEverything_fromFile(A4Reporter.NOP, null, file);
        Command cmd = world.getAllCommands().get(idx);
        A4Options opt = new A4Options();
        opt.solver = new TraceOracle.TraceFactory();
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
        Field sf = A4Solution.class.getDeclaredField("solver");
        sf.setAccessible(true);
        final PardinusSolver orig = (PardinusSolver) sf.get(frame);
        PardinusSolver dumping = new PardinusSolver(orig.options()) {

            @Override
            public Explorer<Solution> solveAll(Formula formula, PardinusBounds bounds) {
                Dumper d = new Dumper();
                d.dump(formula, bounds, orig.options());
                dumped = d.sb.toString();
                return super.solveAll(formula, bounds);
            }
        };
        sf.set(frame, dumping);
        A4Solution sol = frame.solve(A4Reporter.NOP, cmd, new Simplifier(), false);
        try (Writer w = new OutputStreamWriter(new FileOutputStream(prefix + ".kk"), StandardCharsets.UTF_8)) {
            w.write(dumped == null ? "NONE\n" : dumped);
        }
        try (Writer w = new OutputStreamWriter(new FileOutputStream(prefix + ".cnf"), StandardCharsets.UTF_8)) {
            for (StringBuilder b : TraceOracle.blocks) {
                w.write("begin\n");
                w.write(b.toString());
                w.write("end\n");
            }
        }
        String inst = sol.satisfiable() ? TraceOracle.instanceJson(sol) : "null";
        java.nio.file.Files.write(java.nio.file.Paths.get(prefix + ".json"), inst.getBytes(StandardCharsets.UTF_8));
        out.println("OK " + (sol.satisfiable() ? "SAT" : "UNSAT") + " blocks=" + TraceOracle.blocks.size() + " kk=" + (dumped != null));
    }
}
