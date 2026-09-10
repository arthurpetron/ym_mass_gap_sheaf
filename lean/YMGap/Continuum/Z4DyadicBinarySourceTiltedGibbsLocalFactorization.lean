/-
# Common-exterior factorization of source-dependent tilted Gibbs rows

The cutoff-one production row is an integer-tilted coarse Gibbs law, but its
original presentation uses a source-dependent lowering carrier.  This file
first extends that law by zero to the single complete coarse physical
carrier.  It then splits every all-face fusion-path multiplier exactly into

  common exterior factor * packet-disagreement factor.

For two fine sources, the exterior factor is literally the same: it reads
only coarse faces where their four-bit packet totals agree.  Hence every
source dependence in the remaining local factor is carried by the finite
packet-total disagreement list localized in the preceding component theorem.

This is the change-of-measure factorization needed by a connected response
estimate.  It does not bound the normalized row difference, sum a polymer
expansion, construct a continuum measure, or prove a mass gap.

Constructive contract: finite list products and exact rational equivalence
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One complete carrier for every tilted row -/

/-- The tilted numerator weight, extended by its zero multiplicities to the
complete coarse physical carrier. -/
def positivePhysicalSourceTiltedGibbsFullRawWeight
    (S : SlabScalePair) (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling) : Q' :=
  Q'.ofNat
      (spinFourLoweringMultiplicityProduct S
        (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
    S.coarse.physicalTerm targetState

/-- A failed lowering test makes the extended tilted numerator exactly
zero. -/
theorem positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S)
    (targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (htest : spinFourPointwiseLoweringB S
      (wholeSlabFinePacketTotalLabelling S source.1) targetState = false) :
    positivePhysicalSourceTiltedGibbsFullRawWeight
        S source targetState ≈ 0 := by
  let sourceState := wholeSlabFinePacketTotalLabelling S source.1
  have hsource : ∀ faceId, faceId ∈ S.coarse.faceEdges →
      sourceState faceId ≤ 4 := by
    intro faceId hface
    exact wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff source.2.1 faceId hface
  have hraw := spinFourLoweringWholeSlabRawWeight_eqv_zero_of_test_false
    S sourceState targetState hfineCutoff hsource htarget htest
  have hfactor :=
    spinFourLoweringWholeSlabRawWeight_eqv_multiplicity_mul_physicalTerm
      S sourceState targetState htarget
  unfold positivePhysicalSourceTiltedGibbsFullRawWeight
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm hfactor) hraw

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false → value item ≈ 0) →
      listQSum value items ≈ listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false → value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr' (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local value test tail htail)

/-- The source-dependent lowering downset can be removed from the row-mass
formula: the same tilted numerator is summed over one fixed physical
carrier, with excluded states contributing exact zeros. -/
theorem positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S source ≈
      listQSum
        (positivePhysicalSourceTiltedGibbsFullRawWeight S source)
        S.coarse.physicalLabellings := by
  unfold positivePhysicalSourceTiltedGibbsRowMass
    positivePhysicalSourceTiltedGibbsFullRawWeight
    spinFourLoweringTargets
  exact Q'.eqv_symm
    (listQSum_eq_filter_of_zero_local
      (fun targetState =>
        Q'.ofNat
            (spinFourLoweringMultiplicityProduct S
              (wholeSlabFinePacketTotalLabelling S source.1)
              targetState) *
          S.coarse.physicalTerm targetState)
      (spinFourPointwiseLoweringB S
        (wholeSlabFinePacketTotalLabelling S source.1))
      S.coarse.physicalLabellings
      (fun targetState htarget htest =>
        positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
          S hfineCutoff source targetState htarget htest))

/-! ## 2. Agreement and disagreement products -/

/-- Coarse faces on which two fine sources have the same packet total. -/
def finePacketTotalAgreementCoarseFaces
    (S : SlabScalePair) (first second : EdgeLabelling) : List Nat :=
  S.coarse.faceEdges.filter fun faceId =>
    decide
      (wholeSlabFinePacketTotalLabelling S first faceId =
        wholeSlabFinePacketTotalLabelling S second faceId)

/-- The fusion-path multiplier restricted to an explicit list of coarse
faces. -/
def spinFourLoweringMultiplicityProductOn
    (sourceState targetState : EdgeLabelling)
    (faces : List Nat) : Nat :=
  natListProduct
    (fun faceId => spinFourLoweringMultiplicity
      (sourceState faceId) (targetState faceId)) faces

private theorem natListProduct_eq_filter_eq_mul_filter_ne_local
    {A : Type} (left right value : A → Nat) : ∀ items : List A,
    natListProduct value items =
      natListProduct value
          (items.filter fun item => decide (left item = right item)) *
        natListProduct value
          (items.filter fun item => decide (left item ≠ right item))
  | [] => rfl
  | head :: tail => by
      have ih := natListProduct_eq_filter_eq_mul_filter_ne_local
        left right value tail
      by_cases heq : left head = right head
      · simp [natListProduct, heq, ih, Nat.mul_assoc]
      · simp [natListProduct, heq, ih, Nat.mul_left_comm]

/-- Every all-face multiplier splits exactly into its agreement and
disagreement factors. -/
theorem spinFourLoweringMultiplicityProduct_eq_agreement_mul_disagreement
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling)
    (first second : EdgeLabelling) :
    spinFourLoweringMultiplicityProduct S sourceState targetState =
      spinFourLoweringMultiplicityProductOn sourceState targetState
          (finePacketTotalAgreementCoarseFaces S first second) *
        spinFourLoweringMultiplicityProductOn sourceState targetState
          (finePacketTotalDisagreementCoarseFaces S first second) := by
  unfold spinFourLoweringMultiplicityProduct
    spinFourLoweringMultiplicityProductOn
    finePacketTotalAgreementCoarseFaces
    finePacketTotalDisagreementCoarseFaces
  exact natListProduct_eq_filter_eq_mul_filter_ne_local
    (wholeSlabFinePacketTotalLabelling S first)
    (wholeSlabFinePacketTotalLabelling S second)
    (fun faceId => spinFourLoweringMultiplicity
      (sourceState faceId) (targetState faceId))
    S.coarse.faceEdges

/-- On the agreement carrier, the two packet profiles give literally the
same exterior fusion-path multiplier. -/
theorem agreementMultiplicityProduct_eq
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    spinFourLoweringMultiplicityProductOn
        (wholeSlabFinePacketTotalLabelling S first) targetState
        (finePacketTotalAgreementCoarseFaces S first second) =
      spinFourLoweringMultiplicityProductOn
        (wholeSlabFinePacketTotalLabelling S second) targetState
        (finePacketTotalAgreementCoarseFaces S first second) := by
  unfold spinFourLoweringMultiplicityProductOn
  apply natListProduct_congr
  intro faceId hface
  have hparts := List.mem_filter.mp hface
  rw [of_decide_eq_true hparts.2]

/-! ## 3. Exact common-exterior change of measure -/

/-- The common multiplicity background outside the finite disagreement
carrier. -/
def finePacketCommonExteriorMultiplicityProduct
    (S : SlabScalePair) (first second targetState : EdgeLabelling) : Nat :=
  spinFourLoweringMultiplicityProductOn
    (wholeSlabFinePacketTotalLabelling S first) targetState
    (finePacketTotalAgreementCoarseFaces S first second)

/-- The source-specific factor carried only by the finite disagreement
carrier. -/
def finePacketDisagreementMultiplicityProduct
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) : Nat :=
  spinFourLoweringMultiplicityProductOn
    (wholeSlabFinePacketTotalLabelling S source) targetState
    (finePacketTotalDisagreementCoarseFaces S first second)

/-- Full raw tilted weight written as a common exterior Gibbs background
times one source-specific local disagreement factor. -/
def finePacketLocalizedTiltedGibbsRawWeight
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) : Q' :=
  Q'.ofNat
      (finePacketCommonExteriorMultiplicityProduct
        S first second targetState) *
    (Q'.ofNat
        (finePacketDisagreementMultiplicityProduct
          S source first second targetState) *
      S.coarse.physicalTerm targetState)

/-- The first tilted row has the exact common-exterior factorization. -/
theorem firstTiltedGibbsRawWeight_eqv_localized
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S first) targetState) *
      S.coarse.physicalTerm targetState ≈
    finePacketLocalizedTiltedGibbsRawWeight
      S first first second targetState := by
  have hsplit :=
    spinFourLoweringMultiplicityProduct_eq_agreement_mul_disagreement
      S (wholeSlabFinePacketTotalLabelling S first) targetState first second
  unfold finePacketLocalizedTiltedGibbsRawWeight
    finePacketCommonExteriorMultiplicityProduct
    finePacketDisagreementMultiplicityProduct
  rw [hsplit]
  refine Q'.eqv_trans _
    ((Q'.ofNat
        (spinFourLoweringMultiplicityProductOn
          (wholeSlabFinePacketTotalLabelling S first) targetState
          (finePacketTotalAgreementCoarseFaces S first second)) *
      Q'.ofNat
        (spinFourLoweringMultiplicityProductOn
          (wholeSlabFinePacketTotalLabelling S first) targetState
          (finePacketTotalDisagreementCoarseFaces S first second))) *
      S.coarse.physicalTerm targetState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv _ _)
  · exact Q'.mul_assoc_eqv _ _ _

/-- The second tilted row has the same exterior factor and differs only in
its disagreement-carrier multiplier. -/
theorem secondTiltedGibbsRawWeight_eqv_localized
    (S : SlabScalePair) (first second targetState : EdgeLabelling) :
    Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S second) targetState) *
      S.coarse.physicalTerm targetState ≈
    finePacketLocalizedTiltedGibbsRawWeight
      S second first second targetState := by
  have hsplit :=
    spinFourLoweringMultiplicityProduct_eq_agreement_mul_disagreement
      S (wholeSlabFinePacketTotalLabelling S second) targetState first second
  have hagree := agreementMultiplicityProduct_eq
    S first second targetState
  unfold finePacketLocalizedTiltedGibbsRawWeight
    finePacketCommonExteriorMultiplicityProduct
    finePacketDisagreementMultiplicityProduct
  rw [hsplit, ← hagree]
  refine Q'.eqv_trans _
    ((Q'.ofNat
        (spinFourLoweringMultiplicityProductOn
          (wholeSlabFinePacketTotalLabelling S first) targetState
          (finePacketTotalAgreementCoarseFaces S first second)) *
      Q'.ofNat
        (spinFourLoweringMultiplicityProductOn
          (wholeSlabFinePacketTotalLabelling S second) targetState
          (finePacketTotalDisagreementCoarseFaces S first second))) *
      S.coarse.physicalTerm targetState) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (ofNat_mul_eqv _ _)
  · exact Q'.mul_assoc_eqv _ _ _

/-! ## 4. Axiom audit -/

#print axioms positivePhysicalSourceTiltedGibbsFullRawWeight_eqv_zero_of_test_false
#print axioms positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
#print axioms finePacketTotalAgreementCoarseFaces
#print axioms spinFourLoweringMultiplicityProduct_eq_agreement_mul_disagreement
#print axioms agreementMultiplicityProduct_eq
#print axioms finePacketCommonExteriorMultiplicityProduct
#print axioms finePacketDisagreementMultiplicityProduct
#print axioms firstTiltedGibbsRawWeight_eqv_localized
#print axioms secondTiltedGibbsRawWeight_eqv_localized

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
