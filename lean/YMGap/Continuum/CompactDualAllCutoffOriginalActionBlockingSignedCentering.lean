/-
# Centered control of the signed all-cutoff blocking remainder

The exact signed trajectory telescope preserves cancellation between coherent
and fallback sectors, but its analytic terms still need an observable-specific
bound.  The first such reduction is constant-mode cancellation: every
one-step remainder has total mass zero, so its expectation is unchanged after
subtracting an arbitrary rational anchor from the tested observable.

Consequently a centered radius `r` costs only `remainderL1 * r`, rather than
the unscaled total-variation budget.  Physical kernel pullback commutes with
the same centering on every listed source row, so downstream locality or
contraction estimates can be propagated before applying this bound.

This module proves no radius decay, summability, continuum limit, mass gap, or
Clay theorem.  It only exposes the exact finite cancellation consumed by the
signed telescope.

Constructive contract: finite rational sums and exact kernel identities only;
no choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope

namespace
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedCentering

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedTelescope
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact one-step centering -/

/-- Subtract a rational constant from a finite physical observable. -/
def centerObservableAt
    (anchor : Q') (observable : EdgeLabelling → Q') :
    EdgeLabelling → Q' :=
  fun state => observable state + (-anchor)

private theorem remainderObservableExpectation_add
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (left right : EdgeLabelling → Q') :
    remainderObservableExpectation K
        (fun state => left state + right state) ≈
      remainderObservableExpectation K left +
        remainderObservableExpectation K right := by
  unfold remainderObservableExpectation observableExpectation
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        K.remainder state * left state +
          K.remainder state * right state)
      S.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    exact Q'.mul_add_eqv
      (K.remainder state) (left state) (right state)
  · exact listQSum_add
      (fun state => K.remainder state * left state)
      (fun state => K.remainder state * right state)
      S.coarse.physicalLabellings

/-- A constant observable has exactly zero signed remainder expectation. -/
theorem remainderObservableExpectation_constant_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel) (anchor : Q') :
    remainderObservableExpectation K (fun _ => anchor) ≈ 0 := by
  unfold remainderObservableExpectation observableExpectation
  refine Q'.eqv_trans _
    (listQSum K.remainder S.coarse.physicalLabellings * anchor) _ ?_ ?_
  · exact listQSum_mul_right
      K.remainder anchor S.coarse.physicalLabellings
  refine Q'.eqv_trans _ (0 * anchor) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ anchor K.remainder_total_eqv_zero
  · exact Q'.zero_mul_eqv anchor

/-- Subtracting any rational anchor leaves the signed one-step remainder
expectation unchanged. -/
theorem remainderObservableExpectation_eqv_centered
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : EdgeLabelling → Q') (anchor : Q') :
    remainderObservableExpectation K observable ≈
      remainderObservableExpectation K
        (centerObservableAt anchor observable) := by
  refine Q'.eqv_symm (Q'.eqv_trans _
    (remainderObservableExpectation K observable +
      remainderObservableExpectation K (fun _ => -anchor)) _ ?_ ?_)
  · unfold centerObservableAt
    exact remainderObservableExpectation_add
      K observable (fun _ => -anchor)
  refine Q'.eqv_trans _
    (remainderObservableExpectation K observable + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (remainderObservableExpectation_constant_eqv_zero K (-anchor))
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 2. The centered-radius estimate -/

private theorem remainderObservableList_centered_abs_le
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : EdgeLabelling → Q') (anchor radius : Q') :
    ∀ states : List EdgeLabelling,
      (∀ state, state ∈ states →
        Q'.abs (centerObservableAt anchor observable state) ≤ radius) →
      Q'.abs
          (listQSum
            (fun state =>
              K.remainder state *
                centerObservableAt anchor observable state)
            states) ≤
        listQSum (fun state => Q'.abs (K.remainder state)) states *
          radius
  | [], _ => by
      change Q'.abs (0 : Q') ≤ (0 : Q') * radius
      rw [YMGap.Constructive.TrigAdd.abs_zero_eq]
      exact Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv radius))
  | head :: tail, hbound => by
      simp only [listQSum]
      have hhead :
          Q'.abs
              (K.remainder head *
                centerObservableAt anchor observable head) ≤
            Q'.abs (K.remainder head) * radius := by
        refine Q'.le_trans' _ _ _
          (ExpNeg.abs_mul_le
            (K.remainder head)
            (centerObservableAt anchor observable head)) ?_
        exact Q'.mul_le_mul_of_nonneg_left
          (Q'.abs (centerObservableAt anchor observable head))
          radius (Q'.abs (K.remainder head))
          (hbound head List.mem_cons_self)
          (Q'.abs_nonneg (K.remainder head))
      have htail :=
        remainderObservableList_centered_abs_le
          K observable anchor radius tail
          (fun state hstate =>
            hbound state (List.mem_cons_of_mem head hstate))
      refine Q'.le_trans' _ _ _
        (Q'.abs_add_le'
          (K.remainder head *
            centerObservableAt anchor observable head)
          (listQSum
            (fun state =>
              K.remainder state *
                centerObservableAt anchor observable state)
            tail)) ?_
      refine Q'.le_trans' _ _ _
        (Q'.add_le_add hhead htail) ?_
      exact Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            (Q'.abs (K.remainder head))
            (listQSum (fun state => Q'.abs (K.remainder state)) tail)
            radius))

/-- If a coarse observable lies within radius `r` of one rational anchor on
the complete coarse carrier, then its signed one-step remainder costs only
`remainderL1 * r`.  No assumption that `r ≤ 1` is needed. -/
theorem remainderObservableExpectation_abs_le_remainderL1_mul_radius
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (observable : EdgeLabelling → Q') (anchor radius : Q')
    (hbound : ∀ state, state ∈ S.coarse.physicalLabellings →
      Q'.abs (centerObservableAt anchor observable state) ≤ radius) :
    Q'.abs (remainderObservableExpectation K observable) ≤
      K.remainderL1 * radius := by
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (remainderObservableExpectation_eqv_centered
          K observable anchor))) ?_
  unfold remainderObservableExpectation observableExpectation
    SlabScalePair.FiniteSlabKernel.remainderL1
  exact remainderObservableList_centered_abs_le
    K observable anchor radius S.coarse.physicalLabellings hbound

/-! ## 3. Centering commutes with the physical pullback -/

/-- On every listed source row, physical conditional expectation commutes
with subtracting a rational constant. -/
theorem physicalKernelObservablePullback_centered
    (step : AllCutoffOriginalActionStep)
    (observable : EdgeLabelling → Q') (anchor : Q')
    (source : EdgeLabelling)
    (hsource : source ∈ step.pair.fine.physicalLabellings) :
    physicalKernelObservablePullback step
        (centerObservableAt anchor observable) source ≈
      centerObservableAt anchor
        (physicalKernelObservablePullback step observable) source := by
  unfold physicalKernelObservablePullback centerObservableAt
  let kernel := allCutoffPhysicalKernel step.pair step.fineCutoff
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        kernel.kernel source target * observable target +
          kernel.kernel source target * (-anchor))
      step.pair.coarse.physicalLabellings) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    exact Q'.mul_add_eqv
      (kernel.kernel source target) (observable target) (-anchor)
  refine Q'.eqv_trans _
    (listQSum
        (fun target => kernel.kernel source target * observable target)
        step.pair.coarse.physicalLabellings +
      listQSum
        (fun target => kernel.kernel source target * (-anchor))
        step.pair.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_add
      (fun target => kernel.kernel source target * observable target)
      (fun target => kernel.kernel source target * (-anchor))
      step.pair.coarse.physicalLabellings
  refine Q'.add_eqv_congr_left _ _ _ (Q'.eqv_trans _
    (listQSum (kernel.kernel source)
        step.pair.coarse.physicalLabellings * (-anchor)) _ ?_ ?_)
  · exact listQSum_mul_right
      (kernel.kernel source) (-anchor)
      step.pair.coarse.physicalLabellings
  refine Q'.eqv_trans _ (1 * (-anchor)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ (-anchor)
      (kernel.row_normalized source hsource)
  · exact Q'.one_mul_eqv (-anchor)

/-! ## Axiom audit -/

#print axioms centerObservableAt
#print axioms remainderObservableExpectation_constant_eqv_zero
#print axioms remainderObservableExpectation_eqv_centered
#print axioms remainderObservableExpectation_abs_le_remainderL1_mul_radius
#print axioms physicalKernelObservablePullback_centered

end
  YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingSignedCentering
