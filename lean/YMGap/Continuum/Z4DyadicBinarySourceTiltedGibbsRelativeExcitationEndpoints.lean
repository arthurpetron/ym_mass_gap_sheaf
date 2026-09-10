/-
# Relative parity-excitation marks at response endpoints

Absolute target spin is not the normalized activity variable for a
source-dependent lowering row: an extensive parity ground may be forced by
the source.  The correct local coordinate is the number of two-spin raising
steps above that source's parity ground.

This file proves the first exact geometry in that coordinate.  For either
orientation of the symmetrized two-row envelope, every physical face where
the two targets differ is marked in one of two ways:

* the two fine sources already have different packet totals there; or
* at least one target pays a positive parity excitation relative to the
  source assigned to it in that orientation.

In particular, the observable endpoint of every connected active response
pair has such a mark.  This does not yet prove that enough marks occur along
the complete connecting path, sum their weights, or yield a strict rate.

Constructive contract: finite lowering-carrier membership and natural-number
parity arithmetic only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedResponseFraction
import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two oriented relative-excitation marks -/

/-- Relative excitation for the forward envelope orientation
`first → pair.1`, `second → pair.2`. -/
def finePacketForwardRelativeExcitationAt
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Prop :=
  0 < spinFourParityExcitationLevel
      (wholeSlabFinePacketTotalLabelling S first faceId)
      (pair.1 faceId) ∨
    0 < spinFourParityExcitationLevel
      (wholeSlabFinePacketTotalLabelling S second faceId)
      (pair.2 faceId)

/-- Relative excitation for the reverse envelope orientation
`second → pair.1`, `first → pair.2`. -/
def finePacketReverseRelativeExcitationAt
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) (faceId : Nat) : Prop :=
  0 < spinFourParityExcitationLevel
      (wholeSlabFinePacketTotalLabelling S second faceId)
      (pair.1 faceId) ∨
    0 < spinFourParityExcitationLevel
      (wholeSlabFinePacketTotalLabelling S first faceId)
      (pair.2 faceId)

private theorem coarseTargetSpin_le_four_local
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId ≤ 4 := by
  have hsound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htarget
  have hbound := Nat.le_of_lt_succ (hsound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-! ## 2. Equal source parity and unequal targets force excitation -/

/-- Two distinct supported targets over the same cutoff-four source spin
cannot both be at the common parity ground. -/
theorem spinFourEqualSources_target_ne_implies_excitation
    {firstSource secondSource firstTarget secondTarget : Nat}
    (hfirstSource : firstSource ≤ 4)
    (hsecondSource : secondSource ≤ 4)
    (hfirstTarget : firstTarget ≤ 4)
    (hsecondTarget : secondTarget ≤ 4)
    (hfirstLowering : firstTarget ≤ firstSource ∧
      firstTarget % 2 = firstSource % 2)
    (hsecondLowering : secondTarget ≤ secondSource ∧
      secondTarget % 2 = secondSource % 2)
    (hsourceEq : firstSource = secondSource)
    (htargetNe : firstTarget ≠ secondTarget) :
    0 < spinFourParityExcitationLevel firstSource firstTarget ∨
      0 < spinFourParityExcitationLevel secondSource secondTarget := by
  by_cases hfirstGround : firstTarget = firstSource % 2
  · by_cases hsecondGround : secondTarget = secondSource % 2
    · exact False.elim (htargetNe
        (hfirstGround.trans
          ((congrArg (fun value => value % 2) hsourceEq).trans
            hsecondGround.symm)))
    · exact Or.inr
        ((spinFourParityExcitationLevel_pos_iff_ne_ground
          hsecondSource hsecondTarget hsecondLowering).2 hsecondGround)
  · exact Or.inl
      ((spinFourParityExcitationLevel_pos_iff_ne_ground
        hfirstSource hfirstTarget hfirstLowering).2 hfirstGround)

/-! ## 3. Every oriented target disagreement is correctly marked -/

/-- In the forward orientation, target disagreement is either on the source
packet-disagreement carrier or paid by positive relative excitation. -/
theorem finePacketForwardTargetDifference_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hfirstTarget : pair.1 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S first.1))
    (hsecondTarget : pair.2 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S second.1))
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges)
    (htargetNe : pair.1 faceId ≠ pair.2 faceId) :
    faceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketForwardRelativeExcitationAt
        S first.1 second.1 pair faceId := by
  let firstSource := wholeSlabFinePacketTotalLabelling S first.1 faceId
  let secondSource := wholeSlabFinePacketTotalLabelling S second.1 faceId
  by_cases hsourceEq : firstSource = secondSource
  · apply Or.inr
    exact spinFourEqualSources_target_ne_implies_excitation
      (wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff first.2.1 faceId hface)
      (wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff second.2.1 faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff
        ((mem_spinFourLoweringTargets_iff S _ _).mp hfirstTarget).1
        faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff
        ((mem_spinFourLoweringTargets_iff S _ _).mp hsecondTarget).1
        faceId hface)
      (((mem_spinFourLoweringTargets_iff S _ _).mp hfirstTarget).2
        faceId hface)
      (((mem_spinFourLoweringTargets_iff S _ _).mp hsecondTarget).2
        faceId hface)
      hsourceEq htargetNe
  · apply Or.inl
    unfold finePacketTotalDisagreementCoarseFaces
    apply List.mem_filter.mpr
    exact ⟨hface, by simp [firstSource, secondSource, hsourceEq]⟩

/-- The same marked-disagreement theorem in the reverse envelope
orientation. -/
theorem finePacketReverseTargetDifference_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleftTarget : pair.1 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S second.1))
    (hrightTarget : pair.2 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S first.1))
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges)
    (htargetNe : pair.1 faceId ≠ pair.2 faceId) :
    faceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketReverseRelativeExcitationAt
        S first.1 second.1 pair faceId := by
  let firstSource := wholeSlabFinePacketTotalLabelling S second.1 faceId
  let secondSource := wholeSlabFinePacketTotalLabelling S first.1 faceId
  by_cases hsourceEq : firstSource = secondSource
  · apply Or.inr
    exact spinFourEqualSources_target_ne_implies_excitation
      (wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff second.2.1 faceId hface)
      (wholeSlabFinePacketTotalLabelling_le_four
        S hfineCutoff first.2.1 faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff
        ((mem_spinFourLoweringTargets_iff S _ _).mp hleftTarget).1
        faceId hface)
      (coarseTargetSpin_le_four_local S hfineCutoff
        ((mem_spinFourLoweringTargets_iff S _ _).mp hrightTarget).1
        faceId hface)
      (((mem_spinFourLoweringTargets_iff S _ _).mp hleftTarget).2
        faceId hface)
      (((mem_spinFourLoweringTargets_iff S _ _).mp hrightTarget).2
        faceId hface)
      hsourceEq htargetNe
  · apply Or.inl
    unfold finePacketTotalDisagreementCoarseFaces
    apply List.mem_filter.mpr
    exact ⟨hface, by
      simp only [decide_eq_true_eq]
      intro heq
      exact hsourceEq heq.symm⟩

/-! ## 4. Observable endpoint specialization -/

theorem finePacketForwardConnectedActivePair_observable_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hfirstTarget : pair.1 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S first.1))
    (hsecondTarget : pair.2 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S second.1)) :
    observableFaceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketForwardRelativeExcitationAt
        S first.1 second.1 pair observableFaceId := by
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace pair hpair
  exact finePacketForwardTargetDifference_marked
    S hfineCutoff first second pair hfirstTarget hsecondTarget
      observableFaceId hobservableFace path.observable_targetStates_ne

theorem finePacketReverseConnectedActivePair_observable_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hleftTarget : pair.1 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S second.1))
    (hrightTarget : pair.2 ∈ spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S first.1)) :
    observableFaceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketReverseRelativeExcitationAt
        S first.1 second.1 pair observableFaceId := by
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace pair hpair
  exact finePacketReverseTargetDifference_marked
    S hfineCutoff first second pair hleftTarget hrightTarget
      observableFaceId hobservableFace path.observable_targetStates_ne

/-! ## 5. Every nonzero oriented envelope term satisfies the hypotheses -/

/-- Forward summand of the symmetrized raw pair weight. -/
def finePacketForwardLocalizedRawPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketLocalizedTiltedGibbsRawWeight
      S first first second pair.1 *
    finePacketLocalizedTiltedGibbsRawWeight
      S second first second pair.2

/-- Reverse summand of the symmetrized raw pair weight. -/
def finePacketReverseLocalizedRawPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketLocalizedTiltedGibbsRawWeight
      S second first second pair.1 *
    finePacketLocalizedTiltedGibbsRawWeight
      S first first second pair.2

private theorem mul_eqv_zero_of_left_local
    (left right : Q') (hleft : left ≈ 0) : left * right ≈ 0 := by
  refine Q'.eqv_trans _ (0 * right) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hleft
  · exact Q'.zero_mul_eqv right

private theorem mul_eqv_zero_of_right_local
    (left right : Q') (hright : right ≈ 0) : left * right ≈ 0 := by
  refine Q'.eqv_trans _ (left * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hright
  · exact Q'.mul_zero_eqv left

/-- A nonzero forward envelope orientation lies in the two exact lowering
rows assigned by that orientation. -/
theorem finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings)
    (hne : ¬ finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    pair.1 ∈ spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S first.1) ∧
      pair.2 ∈ spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S second.1) := by
  have hphysical := (mem_cartesian_iff
    S.coarse.physicalLabellings S.coarse.physicalLabellings pair).mp hpair
  constructor
  · apply (mem_spinFourLoweringTargets_iff S _ _).mpr
    refine ⟨hphysical.1, ?_⟩
    apply (spinFourPointwiseLoweringB_true_iff S _ _).mp
    cases htest : spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S first.1) pair.1 with
    | true => rfl
    | false =>
        have hfull :=
          positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
            S hfineCutoff first pair.1 hphysical.1 htest
        have hlocal : finePacketLocalizedTiltedGibbsRawWeight
            S first.1 first.1 second.1 pair.1 ≈ 0 :=
          Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (firstTiltedGibbsRawWeight_eqv_localized
                S first.1 second.1 pair.1)) hfull
        exact False.elim (hne
          (mul_eqv_zero_of_left_local _ _ hlocal))
  · apply (mem_spinFourLoweringTargets_iff S _ _).mpr
    refine ⟨hphysical.2, ?_⟩
    apply (spinFourPointwiseLoweringB_true_iff S _ _).mp
    cases htest : spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S second.1) pair.2 with
    | true => rfl
    | false =>
        have hfull :=
          positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
            S hfineCutoff second pair.2 hphysical.2 htest
        have hlocal : finePacketLocalizedTiltedGibbsRawWeight
            S second.1 first.1 second.1 pair.2 ≈ 0 :=
          Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (secondTiltedGibbsRawWeight_eqv_localized
                S first.1 second.1 pair.2)) hfull
        exact False.elim (hne
          (mul_eqv_zero_of_right_local _ _ hlocal))

/-- A nonzero reverse envelope orientation lies in the swapped pair of exact
lowering rows. -/
theorem finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings)
    (hne : ¬ finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    pair.1 ∈ spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S second.1) ∧
      pair.2 ∈ spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S first.1) := by
  have hphysical := (mem_cartesian_iff
    S.coarse.physicalLabellings S.coarse.physicalLabellings pair).mp hpair
  constructor
  · apply (mem_spinFourLoweringTargets_iff S _ _).mpr
    refine ⟨hphysical.1, ?_⟩
    apply (spinFourPointwiseLoweringB_true_iff S _ _).mp
    cases htest : spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S second.1) pair.1 with
    | true => rfl
    | false =>
        have hfull :=
          positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
            S hfineCutoff second pair.1 hphysical.1 htest
        have hlocal : finePacketLocalizedTiltedGibbsRawWeight
            S second.1 first.1 second.1 pair.1 ≈ 0 :=
          Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (secondTiltedGibbsRawWeight_eqv_localized
                S first.1 second.1 pair.1)) hfull
        exact False.elim (hne
          (mul_eqv_zero_of_left_local _ _ hlocal))
  · apply (mem_spinFourLoweringTargets_iff S _ _).mpr
    refine ⟨hphysical.2, ?_⟩
    apply (spinFourPointwiseLoweringB_true_iff S _ _).mp
    cases htest : spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S first.1) pair.2 with
    | true => rfl
    | false =>
        have hfull :=
          positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
            S hfineCutoff first pair.2 hphysical.2 htest
        have hlocal : finePacketLocalizedTiltedGibbsRawWeight
            S first.1 first.1 second.1 pair.2 ≈ 0 :=
          Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (firstTiltedGibbsRawWeight_eqv_localized
                S first.1 second.1 pair.2)) hfull
        exact False.elim (hne
          (mul_eqv_zero_of_right_local _ _ hlocal))

/-- Every nonzero forward contribution on the connected carrier has an
observable endpoint marked by source disagreement or relative excitation. -/
theorem finePacketForwardNonzeroConnectedActivePair_observable_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    observableFaceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketForwardRelativeExcitationAt
        S first.1 second.1 pair observableFaceId := by
  have hfull : pair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings :=
    (List.mem_filter.mp (List.mem_filter.mp hpair).1).1
  have hlowering :=
    finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hfull hne
  exact finePacketForwardConnectedActivePair_observable_marked
    S hfineCutoff first second observableFaceId hobservableFace pair hpair
      hlowering.1 hlowering.2

/-- Every nonzero reverse contribution has the analogous marked observable
endpoint. -/
theorem finePacketReverseNonzeroConnectedActivePair_observable_marked
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId)
    (hne : ¬ finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0) :
    observableFaceId ∈ finePacketTotalDisagreementCoarseFaces
        S first.1 second.1 ∨
      finePacketReverseRelativeExcitationAt
        S first.1 second.1 pair observableFaceId := by
  have hfull : pair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings :=
    (List.mem_filter.mp (List.mem_filter.mp hpair).1).1
  have hlowering :=
    finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
      S hfineCutoff first second pair hfull hne
  exact finePacketReverseConnectedActivePair_observable_marked
    S hfineCutoff first second observableFaceId hobservableFace pair hpair
      hlowering.1 hlowering.2

/-! ## Axiom audit -/

#print axioms finePacketForwardRelativeExcitationAt
#print axioms finePacketReverseRelativeExcitationAt
#print axioms spinFourEqualSources_target_ne_implies_excitation
#print axioms finePacketForwardTargetDifference_marked
#print axioms finePacketReverseTargetDifference_marked
#print axioms finePacketForwardConnectedActivePair_observable_marked
#print axioms finePacketReverseConnectedActivePair_observable_marked
#print axioms finePacketForwardLocalizedRawPairWeight
#print axioms finePacketReverseLocalizedRawPairWeight
#print axioms finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
#print axioms finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
#print axioms finePacketForwardNonzeroConnectedActivePair_observable_marked
#print axioms finePacketReverseNonzeroConnectedActivePair_observable_marked

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
