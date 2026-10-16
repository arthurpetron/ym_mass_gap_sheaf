/-
# Signed observable telescope for all-cutoff original-action blocking

The existing finite trajectory estimate takes an absolute value at every
blocking step and therefore pays the sum of the complete `L1` remainders.
This module records the exact signed alternative before that triangle
inequality.

For a final coarse observable, each later physical kernel supplies its literal
conditional-expectation pullback.  Finite Fubini then proves that the final
blocked-minus-Wilson expectation is exactly the recursive sum of one-step
signed remainder expectations evaluated on those downstream pullbacks.

This is the finite algebraic consumer needed by an observable-specific AF
estimate.  It proves no smallness or summability of the signed terms, does not
identify a continuum observable, and does not prove a mass gap or the Clay
theorem.

Constructive contract: finite rational sums and exact kernel identities only;
no choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact one-step observable pullback -/

/-- Conditional expectation of a coarse observable in one physical kernel
row.  Unlike the enriched one-step pullback, this is the repeatable projected
physical carrier used by `AllCutoffOriginalActionTrajectory`. -/
def physicalKernelObservablePullback
    (step : AllCutoffOriginalActionStep)
    (observable : EdgeLabelling → Q')
    (source : EdgeLabelling) : Q' :=
  listQSum
    (fun target =>
      (allCutoffPhysicalKernel step.pair step.fineCutoff).kernel
          source target *
        observable target)
    step.pair.coarse.physicalLabellings

private theorem finitePushforwardObservableExpectation_eqv_pullback
    {Source Target : Type}
    (sources : List Source) (targets : List Target)
    (sourceMass : Source → Q') (kernel : Source → Target → Q')
    (observable : Target → Q') :
    listQSum
        (fun target =>
          finiteKernelPushforward sources sourceMass kernel target *
            observable target)
        targets ≈
      listQSum
        (fun source =>
          sourceMass source *
            listQSum
              (fun target => kernel source target * observable target)
              targets)
        sources := by
  unfold finiteKernelPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum
          (fun source =>
            (sourceMass source * kernel source target) * observable target)
          sources)
      targets) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun source => sourceMass source * kernel source target)
        (observable target) sources)
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            (sourceMass source * kernel source target) * observable target)
          targets)
      sources) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_swap
        (fun target source =>
          (sourceMass source * kernel source target) * observable target)
        targets sources)
  · apply listQSum_congr_on
    intro source _
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          sourceMass source *
            (kernel source target * observable target))
        targets) _ ?_ ?_
    · apply listQSum_congr_on
      intro target _
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left
        (sourceMass source)
        (fun target => kernel source target * observable target)
        targets

/-- Pushing a mass forward and testing a coarse observable is exactly testing
the source mass against the physical kernel pullback. -/
theorem finitePhysicalPushforwardExpectation_eqv_pullback
    (step : AllCutoffOriginalActionStep)
    (sourceMass : EdgeLabelling → Q')
    (observable : EdgeLabelling → Q') :
    listQSum
        (fun target =>
          finiteKernelPushforward step.pair.fine.physicalLabellings
              sourceMass
              (allCutoffPhysicalKernel
                step.pair step.fineCutoff).kernel target *
            observable target)
        step.pair.coarse.physicalLabellings ≈
      listQSum
        (fun source =>
          sourceMass source *
            physicalKernelObservablePullback step observable source)
        step.pair.fine.physicalLabellings := by
  unfold physicalKernelObservablePullback
  exact finitePushforwardObservableExpectation_eqv_pullback
    step.pair.fine.physicalLabellings
    step.pair.coarse.physicalLabellings sourceMass
    (allCutoffPhysicalKernel step.pair step.fineCutoff).kernel observable

/-- Every physical kernel pullback preserves the constant observable on its
listed fine carrier. -/
theorem physicalKernelObservablePullback_one
    (step : AllCutoffOriginalActionStep)
    (source : EdgeLabelling)
    (hsource : source ∈ step.pair.fine.physicalLabellings) :
    physicalKernelObservablePullback step (fun _ => 1) source ≈ 1 := by
  unfold physicalKernelObservablePullback
  refine Q'.eqv_trans _
    (listQSum
      ((allCutoffPhysicalKernel step.pair step.fineCutoff).kernel source)
      step.pair.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact Q'.mul_one_eqv _
  · exact
      (allCutoffPhysicalKernel step.pair step.fineCutoff).row_normalized
        source hsource

/-! ## 2. The exact signed trajectory sum -/

/-- Recursive signed remainder sum for a final observable.  Every prior
remainder is tested on the exact pullback through all later physical kernels;
no absolute value or per-step total variation has been taken. -/
def signedRemainderTelescope :
    AllCutoffOriginalActionTrajectory →
      (EdgeLabelling → Q') → Q'
  | .single step, observable =>
      remainderObservableExpectation
        (allCutoffPhysicalKernel step.pair step.fineCutoff) observable
  | .append prior next, observable =>
      signedRemainderTelescope prior
          (physicalKernelObservablePullback next observable) +
        remainderObservableExpectation
          (allCutoffPhysicalKernel next.pair next.fineCutoff) observable

private theorem difference_split
    (left middle right : Q') :
    left + (-right) ≈
      (left + (-middle)) + (middle + (-right)) := by
  refine Q'.eqv_trans _
    ((middle + (left + (-middle))) + (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-right)
      (Q'.add_sub_cancel_eqv left middle)
  refine Q'.eqv_trans _
    (((left + (-middle)) + middle) + (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ (-right)
      (Q'.add_comm_eqv middle (left + (-middle)))
  exact Q'.add_assoc_eqv (left + (-middle)) middle (-right)

private theorem signed_telescope_step
    {blocked priorBlocked priorCoarse nextBlocked nextCoarse
      priorTelescope nextRemainder : Q'}
    (hpush : blocked ≈ priorBlocked)
    (hmiddle : priorCoarse ≈ nextBlocked)
    (hnext : nextBlocked + (-nextCoarse) ≈ nextRemainder)
    (hprior : priorBlocked + (-priorCoarse) ≈ priorTelescope) :
    blocked + (-nextCoarse) ≈ priorTelescope + nextRemainder := by
  refine Q'.eqv_trans _
    (priorBlocked + (-nextCoarse)) _
    (Q'.add_eqv_congr_right blocked priorBlocked (-nextCoarse) hpush) ?_
  refine Q'.eqv_trans _
    ((priorBlocked + (-nextBlocked)) +
      (nextBlocked + (-nextCoarse))) _
    (difference_split priorBlocked nextBlocked nextCoarse) ?_
  refine Q'.eqv_trans _
    ((priorBlocked + (-priorCoarse)) + nextRemainder) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.add_eqv_congr_left priorBlocked
        (-nextBlocked) (-priorCoarse)
        (Q'.neg_eqv_congr nextBlocked priorCoarse
          (Q'.eqv_symm hmiddle)))
      hnext
  exact Q'.add_eqv_congr_right
    (priorBlocked + (-priorCoarse)) priorTelescope nextRemainder hprior

/-- **Exact finite signed telescope.**  Along a matched trajectory, the final
blocked-minus-Wilson expectation is the recursive sum of the literal one-step
remainder expectations on their actual downstream-pulled observables. -/
theorem blockedExpectation_sub_coarseWilson_eqv_signedRemainderTelescope
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory)
    (observable : EdgeLabelling → Q') :
    blockedExpectation trajectory observable +
        -(coarseWilsonExpectation trajectory observable) ≈
      signedRemainderTelescope trajectory observable := by
  induction trajectory generalizing observable with
  | single step =>
      let kernel := allCutoffPhysicalKernel step.pair step.fineCutoff
      simpa [blockedExpectation, coarseWilsonExpectation, blockedMass,
        lastStep, signedRemainderTelescope] using
        (blocked_sub_coarseObservableExpectation_eqv_remainder
          kernel observable)
  | append prior next ih =>
      change Matched prior ∧
        (lastStep prior).pair.coarse = next.pair.fine at hmatched
      rcases hmatched with ⟨hpriorMatched, hmatch⟩
      let nextKernel :=
        allCutoffPhysicalKernel next.pair next.fineCutoff
      let pulled := physicalKernelObservablePullback next observable
      let priorBlocked := blockedExpectation prior pulled
      let priorCoarse := coarseWilsonExpectation prior pulled
      let nextBlocked := observableExpectation nextKernel.blockedMass
        next.pair.coarse.physicalLabellings observable
      let nextCoarse := observableExpectation next.pair.coarse.normalizedMass
        next.pair.coarse.physicalLabellings observable
      have hpush : blockedExpectation (.append prior next) observable ≈
          priorBlocked := by
        change
          listQSum
              (fun target =>
                finiteKernelPushforward
                    next.pair.fine.physicalLabellings
                    (blockedMass prior) nextKernel.kernel target *
                  observable target)
              next.pair.coarse.physicalLabellings ≈
            listQSum
              (fun source => blockedMass prior source * pulled source)
              (lastStep prior).pair.coarse.physicalLabellings
        rw [hmatch]
        exact finitePhysicalPushforwardExpectation_eqv_pullback
          next (blockedMass prior) observable
      have hnextBlocked : nextBlocked ≈
          listQSum
            (fun source =>
              next.pair.fine.normalizedMass source * pulled source)
            next.pair.fine.physicalLabellings := by
        change
          listQSum
              (fun target =>
                finiteKernelPushforward
                    next.pair.fine.physicalLabellings
                    next.pair.fine.normalizedMass nextKernel.kernel target *
                  observable target)
              next.pair.coarse.physicalLabellings ≈
            listQSum
              (fun source =>
                next.pair.fine.normalizedMass source * pulled source)
              next.pair.fine.physicalLabellings
        exact finitePhysicalPushforwardExpectation_eqv_pullback
          next next.pair.fine.normalizedMass observable
      have hpriorCoarse : priorCoarse ≈
          listQSum
            (fun source =>
              next.pair.fine.normalizedMass source * pulled source)
            next.pair.fine.physicalLabellings := by
        change
          listQSum
              (fun source =>
                (lastStep prior).pair.coarse.normalizedMass source *
                  pulled source)
              (lastStep prior).pair.coarse.physicalLabellings ≈
            listQSum
              (fun source =>
                next.pair.fine.normalizedMass source * pulled source)
              next.pair.fine.physicalLabellings
        rw [hmatch]
        exact Q'.eqv_refl _
      have hmiddle : priorCoarse ≈ nextBlocked :=
        Q'.eqv_trans _ _ _ hpriorCoarse (Q'.eqv_symm hnextBlocked)
      have hnextRemainder : nextBlocked + (-nextCoarse) ≈
          remainderObservableExpectation nextKernel observable := by
        unfold nextBlocked nextCoarse
        exact blocked_sub_coarseObservableExpectation_eqv_remainder
          nextKernel observable
      change
        blockedExpectation (.append prior next) observable + (-nextCoarse) ≈
          signedRemainderTelescope prior pulled +
            remainderObservableExpectation nextKernel observable
      exact signed_telescope_step hpush hmiddle hnextRemainder
        (ih hpriorMatched pulled)

/-! ## Axiom audit -/

#print axioms physicalKernelObservablePullback
#print axioms finitePhysicalPushforwardExpectation_eqv_pullback
#print axioms physicalKernelObservablePullback_one
#print axioms signedRemainderTelescope
#print axioms blockedExpectation_sub_coarseWilson_eqv_signedRemainderTelescope

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope
