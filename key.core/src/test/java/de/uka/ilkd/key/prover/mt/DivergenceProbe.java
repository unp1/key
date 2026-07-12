/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.mt;

import java.nio.file.Path;
import java.security.MessageDigest;
import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ParallelProver;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProofStarter;

import org.key_project.prover.rules.RuleApp;
import org.key_project.util.helper.FindResources;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

/**
 * DIAGNOSTIC divergence finder for divisionAssoc.key under the parallel prover (probe branch
 * only, never merge). Records the single-core proof as a canonical node sequence (children
 * ordered by their own subtree digest, so legitimate sibling reordering does not count as a
 * difference), then proves the same problem many times under the parallel prover and reports,
 * for each run that DIVERGES (different canonical tree, or does not close), the first node at
 * which the parallel proof departs from the single-core baseline. Never fails: results are read
 * from the DIVP lines in the test output.
 */
public class DivergenceProbe {

    private static final String PROOF = "standard_key/arith/divisionAssoc.key";
    private static final int[] WORKER_COUNTS = { 2, 4 };
    private static final int REPS_PER_COUNT = 200;

    private static String snap;

    @BeforeAll
    static void s() {
        snap = ProofSettings.DEFAULT_SETTINGS.settingsToString();
    }

    @AfterAll
    static void r() {
        ProofSettings.DEFAULT_SETTINGS.loadSettingsFromPropertyString(snap);
    }

    /** A node in canonical order: applied rule + position, plus its canonical subtree digest. */
    private record CanonNode(int serial, String label, String subtreeDigest) {
    }

    @Test
    void findFirstDivergence() throws Exception {
        final Path ex = FindResources.getExampleDirectory();
        Assumptions.assumeTrue(ex != null);
        final Path f = ex.resolve(PROOF);

        final List<CanonNode> baseline = new ArrayList<>();
        final boolean scClosed = prove(f, false, 0, baseline);
        System.out.println("DIVP | SC baseline: closed=" + scClosed + " canonNodes="
            + baseline.size() + " rootDigest="
            + (baseline.isEmpty() ? "?" : baseline.get(0).subtreeDigest.substring(0, 12)));

        int diverged = 0;
        int runs = 0;
        for (int w : WORKER_COUNTS) {
            for (int i = 0; i < REPS_PER_COUNT; i++) {
                runs++;
                final List<CanonNode> mt = new ArrayList<>();
                final boolean closed = prove(f, true, w, mt);
                final boolean sameTree = closed && scClosed && equalCanon(baseline, mt);
                if (sameTree) {
                    continue;
                }
                diverged++;
                System.out.println("DIVP | DIVERGENCE at " + w + "w#" + i + ": closed=" + closed
                    + " canonNodes=" + mt.size() + " (baseline " + baseline.size() + ")");
                reportFirstDivergence(baseline, mt);
                if (diverged >= 5) {
                    System.out.println("DIVP | stopping after 5 divergences");
                    System.out.println("DIVP | SUMMARY: " + diverged + "/" + runs + " diverged");
                    return;
                }
            }
        }
        System.out.println("DIVP | SUMMARY: " + diverged + "/" + runs
            + " runs diverged from the SC baseline (0 = not reproduced in this environment)");
    }

    private static void reportFirstDivergence(List<CanonNode> base, List<CanonNode> mt) {
        final int n = Math.min(base.size(), mt.size());
        for (int i = 0; i < n; i++) {
            if (!base.get(i).label.equals(mt.get(i).label)) {
                System.out.println("DIVP |   first differing canonical node #" + i);
                System.out.println(
                    "DIVP |     SC : serial=" + base.get(i).serial + "  " + base.get(i).label);
                System.out.println(
                    "DIVP |     MT : serial=" + mt.get(i).serial + "  " + mt.get(i).label);
                for (int k = Math.max(0, i - 3); k < i; k++) {
                    System.out.println("DIVP |     (both agree #" + k + "): " + base.get(k).label);
                }
                return;
            }
        }
        System.out.println("DIVP |   trees agree on the first " + n
            + " canonical nodes; they differ only in length (SC=" + base.size() + " MT="
            + mt.size() + ") -> the shorter run stopped early");
    }

    private static boolean equalCanon(List<CanonNode> a, List<CanonNode> b) {
        if (a.size() != b.size()) {
            return false;
        }
        for (int i = 0; i < a.size(); i++) {
            if (!a.get(i).label.equals(b.get(i).label)) {
                return false;
            }
        }
        return true;
    }

    /** Proves the file and fills {@code out} with the canonical node sequence. Returns closed. */
    private static boolean prove(Path f, boolean par, int w, List<CanonNode> out) throws Exception {
        final String pp = System.getProperty(ParallelProver.PARALLEL_PROPERTY);
        final String pt = System.getProperty(ParallelProver.THREADS_PROPERTY);
        if (par) {
            System.setProperty(ParallelProver.PARALLEL_PROPERTY, "true");
            System.setProperty(ParallelProver.THREADS_PROPERTY, Integer.toString(w));
        } else {
            System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
        }
        KeYEnvironment<?> env = null;
        try {
            env = KeYEnvironment.load(f);
            final Proof p = env.getLoadedProof();
            final ProofStarter st = new ProofStarter(false);
            st.init(p);
            st.start();
            emit(p.root(), out);
            return p.closed();
        } finally {
            if (env != null) {
                env.dispose();
            }
            if (pp == null) {
                System.clearProperty(ParallelProver.PARALLEL_PROPERTY);
            } else {
                System.setProperty(ParallelProver.PARALLEL_PROPERTY, pp);
            }
            if (pt == null) {
                System.clearProperty(ParallelProver.THREADS_PROPERTY);
            } else {
                System.setProperty(ParallelProver.THREADS_PROPERTY, pt);
            }
        }
    }

    /** Emits the subtree in canonical pre-order (children sorted by subtree digest). */
    private static String emit(Node node, List<CanonNode> out) {
        final int c = node.childrenCount();
        final String[] digs = new String[c];
        final List<List<CanonNode>> childSeqs = new ArrayList<>(c);
        final List<Integer> order = new ArrayList<>(c);
        for (int i = 0; i < c; i++) {
            final List<CanonNode> seq = new ArrayList<>();
            digs[i] = emit(node.child(i), seq);
            childSeqs.add(seq);
            order.add(i);
        }
        order.sort((x, y) -> digs[x].compareTo(digs[y]));

        final String label = labelOf(node);
        final StringBuilder canon = new StringBuilder(label).append('(');
        for (int o : order) {
            canon.append(digs[o]).append(',');
        }
        canon.append(')');
        final String myDigest = sha256(canon.toString());

        out.add(new CanonNode(node.serialNr(), label, myDigest));
        for (int o : order) {
            out.addAll(childSeqs.get(o));
        }
        return myDigest;
    }

    private static String labelOf(Node node) {
        final RuleApp app = node.getAppliedRuleApp();
        if (app == null) {
            return node.isClosed() ? "<closed>" : "<open>";
        }
        String pos = "";
        try {
            if (app.posInOccurrence() != null) {
                pos = "@" + app.posInOccurrence().subTerm();
            }
        } catch (Throwable ignore) {
            // position printing is best-effort; the rule name is the primary signal
        }
        final String p = pos.length() > 60 ? pos.substring(0, 60) : pos;
        return app.rule().name() + p;
    }

    private static String sha256(String s) {
        try {
            final MessageDigest md = MessageDigest.getInstance("SHA-256");
            final byte[] d = md.digest(s.getBytes(java.nio.charset.StandardCharsets.UTF_8));
            final StringBuilder sb = new StringBuilder(64);
            for (byte b : d) {
                sb.append(Character.forDigit((b >> 4) & 0xF, 16));
                sb.append(Character.forDigit(b & 0xF, 16));
            }
            return sb.toString();
        } catch (Exception e) {
            throw new RuntimeException(e);
        }
    }
}
