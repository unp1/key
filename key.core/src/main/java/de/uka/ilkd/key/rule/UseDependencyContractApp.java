/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

public class UseDependencyContractApp<T extends UseDependencyContractRule>
        extends AbstractContractRuleApp<T> {

    private final PosInOccurrence step;
    private List<LocationVariable> heapContext;

    public UseDependencyContractApp(UseDependencyContractRule builtInRule, PosInOccurrence pio) {
        this(builtInRule, pio, null, null);
    }

    public UseDependencyContractApp(UseDependencyContractRule builtInRule, PosInOccurrence pio,
            Contract instantiation, PosInOccurrence step) {
        this(builtInRule, pio, ImmutableList.nil(), instantiation, step);
    }

    public UseDependencyContractApp(UseDependencyContractRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, Contract contract,
            PosInOccurrence step) {
        // weigl: why is this unchecked cast needed?
        super((T) rule, pio, ifInsts, contract);
        this.step = step;
    }

    public UseDependencyContractApp<T> replacePos(PosInOccurrence newPos) {
        return new UseDependencyContractApp<>(rule(), newPos, ifInsts, instantiation, step);
    }

    public boolean isSufficientlyComplete() {
        return pio != null && instantiation != null && !ifInsts.isEmpty();
    }

    public boolean complete() {
        return super.complete() && step != null;
    }

    private UseDependencyContractApp computeStep(Sequent seq, Services services) {
        assert this.step == null;
        final List<PosInOccurrence> steps = UseDependencyContractRule
                .getSteps(this.getHeapContext(), this.posInOccurrence(), seq, services);
        PosInOccurrence l_step =
            UseDependencyContractRule.findStepInIfInsts(steps, this);
        if (l_step == null) {
            // The step this rule application was costed with (recorded by
            // DependencyContractFeature at cost-computation time) is no longer part of the
            // sequent: another rule application on this goal has rewritten it while the
            // application waited in the rule-application queue. The rule application is
            // stale. This is a legal state of the queue protocol -- the queue tracks only
            // the find position, not the assumes positions, so it can happen with any
            // prover: the multi-core prover reaches it regularly (the per-goal rule order
            // varies with worker timing), a single-core search can reach it as well.
            //
            // Design decision: staleness is TOLERATED here, not prevented. Leaving the
            // step unset keeps complete() false, so the caller discards the application
            // and the next cost computation offers the rule again, with a step from the
            // then-current sequent -- the same discard-and-recost channel every other
            // stale queue entry uses (see BuiltInRuleAppContainer.completeRuleApp). The
            // two preventive alternatives are deliberately not used: tracking the assumes
            // positions with formula tags and refreshing eagerly would add queue machinery
            // only to arrive at the same re-costing; and recomputing a step HERE, at
            // completion time, would bypass the strategy's step policy (in particular
            // removePreviouslyUsedSteps in DependencyContractFeature) and could re-apply
            // the contract with a step the strategy deliberately excluded.
            return this;
        }
        return setStep(l_step);
    }


    public PosInOccurrence step() {
        return step;
    }

    public UseDependencyContractApp<T> setStep(PosInOccurrence p_step) {
        assert this.step == null;
        return new UseDependencyContractApp<>(rule(), posInOccurrence(), assumesInsts(),
            instantiation,
            p_step);
    }

    @Override
    public UseDependencyContractApp<T> setContract(Contract contract) {
        return new UseDependencyContractApp<>(rule(), posInOccurrence(), ifInsts, contract,
            step);
    }

    public UseDependencyContractApp<T> tryToInstantiate(Goal goal) {
        if (heapContext == null) {
            heapContext = HeapContext.getModifiableHeaps(goal.proof().getServices(), false);
        }
        if (complete()) {
            return this;
        }
        UseDependencyContractApp app = this;

        final Services services = goal.proof().getServices();

        app = tryToInstantiateContract(services);

        if (!app.complete() && app.isSufficientlyComplete()) {
            app = app.computeStep(goal.sequent(), services);
        }
        return app;
    }

    public UseDependencyContractApp tryToInstantiateContract(final Services services) {
        final var focus = posInOccurrence().subTerm();
        if (!(focus.op() instanceof IObserverFunction target))
        // TODO: find more appropriate exception
        {
            throw new RuntimeException(
                "Dependency contract rule is not applicable to term " + focus);
        }

        final Term selfTerm;
        final KeYJavaType kjt;

        if (target.isStatic()) {
            selfTerm = null;
            kjt = target.getContainerType();
        } else {
            if (getHeapContext() == null) {
                heapContext = HeapContext.getModifiableHeaps(services, false);
            }
            selfTerm = focus.sub(target.getStateCount() * target.getHeapCount(services));
            kjt = services.getJavaInfo().getKeYJavaType(selfTerm.sort());
        }
        ImmutableSet<Contract> contracts =
            UseDependencyContractRule.getApplicableContracts(services, kjt, target);

        if (!contracts.isEmpty()) {
            UseDependencyContractApp r = setContract(contracts.iterator().next());
            if (r.getHeapContext() == null) {
                r.heapContext = HeapContext.getModifiableHeaps(services, false);
            }
            return r;
        }
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
        return heapContext;
    }

    @Override
    public IObserverFunction getObserverFunction(Services services) {
        final var op = posInOccurrence().subTerm().op();
        return (IObserverFunction) (op instanceof IObserverFunction ? op : null);
    }



    @Override
    public UseDependencyContractApp setAssumesInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        // return new UseDependencyContractApp(builtInRule, pio, ifInsts, instantiation, step);
    }



}
