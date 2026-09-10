/-
# Normalize the joint parity-ground reference by literal row summands

Every positive cutoff-one source row contains its geometric parity target as
a literal positive summand.  This file pairs those two ground targets in the
same forward/reverse orientation used by the connected envelope.  Their
excitation excess is exactly zero, so the product of the two ground masses is
exactly the parity-ground heat power times the oriented coupling-one ground
weight.

The ground product is bounded by the exact two-row normalization.  Dividing
the reference left by the heat suppression factor by this literal positive
ground product defines the remaining reference-congestion ratio.  One actual
joint summand is then bounded by

`suppression * congestion * rowNormalization`.

This is the denominator cancellation needed before counting entropy.  No
bound on the congestion ratio, contour sum, or volume uniformity is asserted.

Constructive contract: exact finite-carrier identities and positivity-guarded
rational division only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
import YMGap.Continuum.Z4DyadicBinarySourceParityGroundState

namespace YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listNatWeight_eq_zero_local {A : Type}
    (value : A → Nat) : ∀ items : List A,
    (∀ item, item ∈ items → value item = 0) →
      listNatWeight value items = 0
  | [], _ => rfl
  | head :: tail, hzero => by
      simp only [listNatWeight, hzero head List.mem_cons_self,
        Nat.zero_add]
      exact listNatWeight_eq_zero_local value tail
        (fun item hitem =>
          hzero item (List.mem_cons_of_mem head hitem))

/-! ## 1. The oriented pair of literal parity-ground targets -/

def finePacketOrientedParityGroundTargetPair
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : EdgeLabelling × EdgeLabelling :=
  match orientation with
  | .forward =>
      (cutoffOneCoarseParityState S first,
        cutoffOneCoarseParityState S second)
  | .reverse =>
      (cutoffOneCoarseParityState S second,
        cutoffOneCoarseParityState S first)

theorem finePacketOrientedParityGroundTargetPair_lowering
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedLoweringPair S orientation first.1 second.1
      (finePacketOrientedParityGroundTargetPair
        S orientation first.1 second.1) := by
  cases orientation with
  | forward =>
      exact ⟨
        cutoffOneCoarseParityState_mem_totalLoweringTargets
          S hfineCutoff first.2.1,
        cutoffOneCoarseParityState_mem_totalLoweringTargets
          S hfineCutoff second.2.1⟩
  | reverse =>
      exact ⟨
        cutoffOneCoarseParityState_mem_totalLoweringTargets
          S hfineCutoff second.2.1,
        cutoffOneCoarseParityState_mem_totalLoweringTargets
          S hfineCutoff first.2.1⟩

/-- The oriented geometric ground pair has exactly zero target excitation
Casimir excess. -/
theorem finePacketOrientedParityGroundTargetPair_totalCasimirExcess_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedTotalTargetCasimirExcess
        S orientation first.1 second.1
        (finePacketOrientedParityGroundTargetPair
          S orientation first.1 second.1) = 0 := by
  unfold finePacketOrientedTotalTargetCasimirExcess
  apply listNatWeight_eq_zero_local
  intro faceId hface
  cases orientation with
  | forward =>
      simp only [finePacketOrientedParityGroundTargetPair,
        finePacketOrientedTargetCasimirExcessAt,
        finePacketOrientedLeftSource, finePacketOrientedRightSource]
      rw [cutoffOneCoarseParityState_face_eq_total_mod_two
          S hfineCutoff first.2.1 hface,
        cutoffOneCoarseParityState_face_eq_total_mod_two
          S hfineCutoff second.2.1 hface]
      simp [spinFourParityExcitationCasimirExcess,
        spinFourParityGroundCasimirExponent]
  | reverse =>
      simp only [finePacketOrientedParityGroundTargetPair,
        finePacketOrientedTargetCasimirExcessAt,
        finePacketOrientedLeftSource, finePacketOrientedRightSource]
      rw [cutoffOneCoarseParityState_face_eq_total_mod_two
          S hfineCutoff second.2.1 hface,
        cutoffOneCoarseParityState_face_eq_total_mod_two
          S hfineCutoff first.2.1 hface]
      simp [spinFourParityExcitationCasimirExcess,
        spinFourParityGroundCasimirExponent]

/-! ## 2. Ground products are the exact parity-ground reference normalizer -/

def finePacketOrientedParityGroundReferenceNormalizationMass
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling) : Q' :=
  qpow S.coarse.coupling
      (finePacketOrientedTotalTargetParityGroundCasimir
        S orientation first second) *
    finePacketOrientedUnitCouplingTargetRawPairWeight
      S orientation first second
      (finePacketOrientedParityGroundTargetPair
        S orientation first second)

private theorem parityGroundMass_eqv_forwardLocalized
    (S : SlabScalePair) (first second : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundMass S first ≈
      finePacketLocalizedTiltedGibbsRawWeight
        S first.1 first.1 second.1
          (cutoffOneCoarseParityState S first.1) := by
  unfold positivePhysicalSourceParityGroundMass
  exact firstTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 (cutoffOneCoarseParityState S first.1)

private theorem parityGroundMass_eqv_secondLocalized
    (S : SlabScalePair) (first second : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundMass S second ≈
      finePacketLocalizedTiltedGibbsRawWeight
        S second.1 first.1 second.1
          (cutoffOneCoarseParityState S second.1) := by
  unfold positivePhysicalSourceParityGroundMass
  exact secondTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 (cutoffOneCoarseParityState S second.1)

private theorem parityGroundMassProduct_eqv_orientedLocalized
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundMass S first *
        positivePhysicalSourceParityGroundMass S second ≈
      finePacketOrientedLocalizedRawPairWeight
        S orientation first.1 second.1
        (finePacketOrientedParityGroundTargetPair
          S orientation first.1 second.1) := by
  cases orientation with
  | forward =>
      exact qmul_congr_local
        (parityGroundMass_eqv_forwardLocalized S first second)
        (parityGroundMass_eqv_secondLocalized S first second)
  | reverse =>
      refine Q'.eqv_trans _
        (positivePhysicalSourceParityGroundMass S second *
          positivePhysicalSourceParityGroundMass S first) _
        (Q'.mul_comm_eqv _ _) ?_
      exact qmul_congr_local
        (parityGroundMass_eqv_secondLocalized S first second)
        (parityGroundMass_eqv_forwardLocalized S first second)

/-- The product of the two literal positive ground summands is exactly the
oriented parity-ground reference normalizer. -/
theorem positivePhysicalSourceParityGroundMassProduct_eqv_referenceNormalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceParityGroundMass S first *
        positivePhysicalSourceParityGroundMass S second ≈
      finePacketOrientedParityGroundReferenceNormalizationMass
        S orientation first.1 second.1 := by
  have hlowering := finePacketOrientedParityGroundTargetPair_lowering
    S hfineCutoff orientation first second
  have hlocalized := parityGroundMassProduct_eqv_orientedLocalized
    S orientation first second
  have hfactor :=
    finePacketOrientedLocalizedRawPairWeight_eqv_ground_mul_excitation_mul_unit
      S hfineCutoff orientation first second
      (finePacketOrientedParityGroundTargetPair
        S orientation first.1 second.1) hlowering
  have hexcess :=
    finePacketOrientedParityGroundTargetPair_totalCasimirExcess_zero
      S hfineCutoff orientation first second
  rw [hexcess] at hfactor
  refine Q'.eqv_trans _ _ _ hlocalized
    (Q'.eqv_trans _ _ _ hfactor ?_)
  unfold finePacketOrientedParityGroundReferenceNormalizationMass
  rw [qpow_zero]
  exact Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)

theorem finePacketOrientedParityGroundReferenceNormalizationMass_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    (0 : Q') < finePacketOrientedParityGroundReferenceNormalizationMass
      S orientation first.1 second.1 := by
  have hproduct : (0 : Q') <
      positivePhysicalSourceParityGroundMass S first *
        positivePhysicalSourceParityGroundMass S second :=
    Q'.mul_pos
      (positivePhysicalSourceParityGroundMass_pos
        S hfineCutoff hcoarseCoupling first)
      (positivePhysicalSourceParityGroundMass_pos
        S hfineCutoff hcoarseCoupling second)
  exact Q'.pos_of_lt_of_le hproduct
    (Q'.le_of_eqv
      (positivePhysicalSourceParityGroundMassProduct_eqv_referenceNormalization
        S hfineCutoff orientation first second))

/-- The literal ground reference normalizer is bounded by the complete
two-row normalization, without any volume-dependent constant. -/
theorem finePacketOrientedParityGroundReferenceNormalizationMass_le_rowNormalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedParityGroundReferenceNormalizationMass
        S orientation first.1 second.1 ≤
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  have hfirst := positivePhysicalSourceParityGroundMass_le_rowMass
    S hfineCutoff hcoarseCoupling first
  have hsecond := positivePhysicalSourceParityGroundMass_le_rowMass
    S hfineCutoff hcoarseCoupling second
  have hsecond0 : (0 : Q') ≤ positivePhysicalSourceParityGroundMass S second :=
    Q'.le_of_lt
      (positivePhysicalSourceParityGroundMass_pos
        S hfineCutoff hcoarseCoupling second)
  have hrowFirst0 : (0 : Q') ≤
      positivePhysicalSourceTiltedGibbsRowMass S first :=
    Q'.le_of_lt
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling first)
  have hproduct :
      positivePhysicalSourceParityGroundMass S first *
          positivePhysicalSourceParityGroundMass S second ≤
        positivePhysicalSourceTiltedGibbsRowMass S first *
          positivePhysicalSourceTiltedGibbsRowMass S second := by
    refine Q'.le_trans' _
      (positivePhysicalSourceTiltedGibbsRowMass S first *
        positivePhysicalSourceParityGroundMass S second) _ ?_ ?_
    · exact Q'.mul_le_mul_of_nonneg_right _ _ _ hfirst hsecond0
    · exact Q'.mul_le_mul_of_nonneg_left _ _ _ hsecond hrowFirst0
  unfold finePacketOrientedEnvelopeNormalizationMass
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (positivePhysicalSourceParityGroundMassProduct_eqv_referenceNormalization
        S hfineCutoff orientation first second)) hproduct

/-! ## 3. Isolate the remaining reference congestion ratio -/

private theorem finePacketLocalizedUnitCouplingTargetRawWeight_nonnegative
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (0 : Q') ≤ finePacketLocalizedUnitCouplingTargetRawWeight
      S source first second targetState := by
  unfold finePacketLocalizedUnitCouplingTargetRawWeight
  exact Q'.mul_nonneg _ _ (zero_le_ofNat _)
    (Q'.mul_nonneg _ _ (zero_le_ofNat _)
      (slabParametricKPhysicalTerm_nonnegative
        (by decide) S.coarse.cutoff S.coarse.extent targetState))

private theorem finePacketOrientedUnitCouplingTargetRawPairWeight_nonnegative
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedUnitCouplingTargetRawPairWeight
      S orientation first second pair := by
  cases orientation with
  | forward | reverse =>
      exact Q'.mul_nonneg _ _
        (finePacketLocalizedUnitCouplingTargetRawWeight_nonnegative S _ _ _ _)
        (finePacketLocalizedUnitCouplingTargetRawWeight_nonnegative S _ _ _ _)

private theorem finePacketFineSourceUnitCouplingPairWeight_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling) :
    (0 : Q') ≤ finePacketFineSourceUnitCouplingPairWeight S first second := by
  unfold finePacketFineSourceUnitCouplingPairWeight
    fineUnitCouplingPhysicalTerm
  exact Q'.mul_nonneg _ _
    (slabParametricKPhysicalTerm_nonnegative
      (by decide) S.fine.cutoff S.fine.extent first)
    (slabParametricKPhysicalTerm_nonnegative
      (by decide) S.fine.cutoff S.fine.extent second)

theorem finePacketOrientedJointParityGroundReferenceWeight_nonnegative
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedJointParityGroundReferenceWeight
      S orientation first second pair := by
  unfold finePacketOrientedJointParityGroundReferenceWeight
  exact Q'.mul_nonneg _ _
    (qpow_nonneg S.coarse.coupling S.coarse.coupling_nonnegative _)
    (Q'.mul_nonneg _ _
      (finePacketFineSourceUnitCouplingPairWeight_nonnegative
        S first second)
      (finePacketOrientedUnitCouplingTargetRawPairWeight_nonnegative
        S orientation first second pair))

/-- The sole factor left after exact heat suppression and literal ground-row
normalization.  Its numerator and denominator are both fully explicit finite
SU(2) weights. -/
def finePacketOrientedJointReferenceCongestionRatio
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  Q'.divPos
    (finePacketOrientedJointParityGroundReferenceWeight
      S orientation first.1 second.1 pair)
    (finePacketOrientedParityGroundReferenceNormalizationMass
      S orientation first.1 second.1)
    (finePacketOrientedParityGroundReferenceNormalizationMass_pos
      S hfineCutoff hcoarseCoupling orientation first second)

theorem finePacketOrientedJointReferenceCongestionRatio_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedJointReferenceCongestionRatio
      S hfineCutoff hcoarseCoupling orientation first second pair := by
  unfold finePacketOrientedJointReferenceCongestionRatio Q'.divPos
  exact Q'.mul_nonneg _ _
    (finePacketOrientedJointParityGroundReferenceWeight_nonnegative
      S orientation first.1 second.1 pair)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (finePacketOrientedParityGroundReferenceNormalizationMass_pos
          S hfineCutoff hcoarseCoupling orientation first second)))

/-- The parity-ground reference is at most its explicit congestion ratio
times the exact two-row normalization. -/
theorem finePacketOrientedJointParityGroundReferenceWeight_le_congestion_mul_rowNormalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedJointParityGroundReferenceWeight
        S orientation first.1 second.1 pair ≤
      finePacketOrientedJointReferenceCongestionRatio
          S hfineCutoff hcoarseCoupling orientation first second pair *
        finePacketOrientedEnvelopeNormalizationMass S first second := by
  let numerator := finePacketOrientedJointParityGroundReferenceWeight
    S orientation first.1 second.1 pair
  let ground := finePacketOrientedParityGroundReferenceNormalizationMass
    S orientation first.1 second.1
  let ratio := finePacketOrientedJointReferenceCongestionRatio
    S hfineCutoff hcoarseCoupling orientation first second pair
  let normalization := finePacketOrientedEnvelopeNormalizationMass
    S first second
  have hgroundPos : (0 : Q') < ground :=
    finePacketOrientedParityGroundReferenceNormalizationMass_pos
      S hfineCutoff hcoarseCoupling orientation first second
  have hcancel : ratio * ground ≈ numerator := by
    exact Q'.divPos_mul_eqv numerator ground hgroundPos
  have hgroundLe : ground ≤ normalization :=
    finePacketOrientedParityGroundReferenceNormalizationMass_le_rowNormalization
      S hfineCutoff hcoarseCoupling orientation first second
  have hratio0 : (0 : Q') ≤ ratio :=
    finePacketOrientedJointReferenceCongestionRatio_nonnegative
      S hfineCutoff hcoarseCoupling orientation first second pair
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcancel)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hgroundLe hratio0)

/-! ## 4. Pointwise normalized joint bound -/

private theorem finePacketOrientedJointSuppressionFactor_nonnegative
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedJointSuppressionFactor
      S orientation first second pair := by
  unfold finePacketOrientedJointSuppressionFactor
  exact Q'.mul_nonneg _ _
    (qpow_nonneg S.fine.coupling S.fine.coupling_nonnegative _)
    (qpow_nonneg S.coarse.coupling S.coarse.coupling_nonnegative _)

/-- One complete actual joint source-target summand is bounded by heat
suppression times the explicit remaining congestion ratio times the exact
two-row normalization.  This is the pointwise interface for the entropy sum. -/
theorem finePacketOrientedJointGibbsRawPairWeight_le_suppression_mul_congestion_mul_rowNormalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedJointGibbsRawPairWeight
        S orientation first.1 second.1 pair ≤
      (finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedJointReferenceCongestionRatio
          S hfineCutoff hcoarseCoupling orientation first second pair) *
        finePacketOrientedEnvelopeNormalizationMass S first second := by
  have hfactor :=
    finePacketOrientedJointGibbsRawPairWeight_eqv_suppression_mul_reference
      S hfineCutoff orientation first second pair hlowering
  have hreference :=
    finePacketOrientedJointParityGroundReferenceWeight_le_congestion_mul_rowNormalization
      S hfineCutoff hcoarseCoupling orientation first second pair
  have hsuppression0 :=
    finePacketOrientedJointSuppressionFactor_nonnegative
      S orientation first.1 second.1 pair
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hreference hsuppression0) ?_)
  exact Q'.ge_of_eqv (Q'.mul_assoc_eqv _ _ _)

/-! ## 5. Axiom audit -/

#print axioms finePacketOrientedParityGroundTargetPair
#print axioms finePacketOrientedParityGroundTargetPair_lowering
#print axioms finePacketOrientedParityGroundTargetPair_totalCasimirExcess_zero
#print axioms finePacketOrientedParityGroundReferenceNormalizationMass
#print axioms positivePhysicalSourceParityGroundMassProduct_eqv_referenceNormalization
#print axioms finePacketOrientedParityGroundReferenceNormalizationMass_pos
#print axioms finePacketOrientedParityGroundReferenceNormalizationMass_le_rowNormalization
#print axioms finePacketOrientedJointParityGroundReferenceWeight_nonnegative
#print axioms finePacketOrientedJointReferenceCongestionRatio
#print axioms finePacketOrientedJointReferenceCongestionRatio_nonnegative
#print axioms finePacketOrientedJointParityGroundReferenceWeight_le_congestion_mul_rowNormalization
#print axioms finePacketOrientedJointGibbsRawPairWeight_le_suppression_mul_congestion_mul_rowNormalization

end YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization
