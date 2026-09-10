/-
# Exact heat-exponent factorization of the joint binary response weight

The connected contour activity found in the preceding modules is paid by two
different physical Gibbs factors: cutoff-one fine source masses and cutoff-four
coarse target masses.  This file factors the corresponding heat powers out of
the actual oriented joint summand without estimating any remaining factor.

The coarse target exponent is then split into its source-parity ground and its
SU(2) excitation excess.  Thus every oriented joint summand is exactly

`(fine source power * coarse excitation power) * parity-ground reference`.

Both lattice couplings occur explicitly.  The parity-ground reference still
depends on the coarse coupling, and no uniformity, strict rate, normalization,
or contour summation is asserted here.

Constructive contract: exact rational identities and finite physical-carrier
membership only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess

namespace YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-! ## 1. One localized target row at coupling one -/

/-- The localized target weight with precisely the same lowering
multiplicities and corrected-slab geometry, but coarse heat coupling one. -/
def finePacketLocalizedUnitCouplingTargetRawWeight
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) : Q' :=
  Q'.ofNat
      (finePacketCommonExteriorMultiplicityProduct
        S first second targetState) *
    (Q'.ofNat
        (finePacketDisagreementMultiplicityProduct
          S source first second targetState) *
      slabParametricKPhysicalTerm
        1 S.coarse.cutoff S.coarse.extent targetState)

/-- One localized target row factors into its complete coarse Casimir heat
power and the otherwise identical coupling-one target weight. -/
theorem finePacketLocalizedTiltedGibbsRawWeight_eqv_coarseHeatPower_mul_unit
    (S : SlabScalePair) (source first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings) :
    finePacketLocalizedTiltedGibbsRawWeight
        S source first second targetState ≈
      qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent targetState) *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S source first second targetState := by
  have hbounded : targetState ∈ boundedEdgeLabellings S.coarse.cutoff
      (slabPhysicalFaceEdges S.coarse.extent) := by
    simpa only [SlabPhysicalData.physicalLabellings,
      SlabPhysicalData.faceEdges] using htarget
  have hterm := slabParametricKPhysicalTerm_eqv_power_mul_atOne
    S.coarse.coupling S.coarse.cutoff S.coarse.extent
      targetState hbounded
  unfold finePacketLocalizedTiltedGibbsRawWeight
    finePacketLocalizedUnitCouplingTargetRawWeight
    SlabPhysicalData.physicalTerm
  refine Q'.eqv_trans _
    (Q'.ofNat
        (finePacketCommonExteriorMultiplicityProduct
          S first second targetState) *
      (Q'.ofNat
          (finePacketDisagreementMultiplicityProduct
            S source first second targetState) *
        (qpow S.coarse.coupling
            (slabPhysicalCasimirExponent S.coarse.extent targetState) *
          slabParametricKPhysicalTerm
            1 S.coarse.cutoff S.coarse.extent targetState))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.mul_eqv_congr_left _ _ _ hterm)
  · ring_qeqv

/-! ## 2. The complete oriented target pair -/

def finePacketOrientedLocalizedRawPairWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  match orientation with
  | .forward => finePacketForwardLocalizedRawPairWeight S first second pair
  | .reverse => finePacketReverseLocalizedRawPairWeight S first second pair

def finePacketOrientedUnitCouplingTargetRawPairWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  match orientation with
  | .forward =>
      finePacketLocalizedUnitCouplingTargetRawWeight
          S first first second pair.1 *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S second first second pair.2
  | .reverse =>
      finePacketLocalizedUnitCouplingTargetRawWeight
          S second first second pair.1 *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S first first second pair.2

private theorem localizedTargetPair_eqv_totalCoarseHeatPower_mul_unit
    (S : SlabScalePair)
    (leftSource rightSource first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    finePacketLocalizedTiltedGibbsRawWeight
          S leftSource first second pair.1 *
        finePacketLocalizedTiltedGibbsRawWeight
          S rightSource first second pair.2 ≈
      qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.1 +
            slabPhysicalCasimirExponent S.coarse.extent pair.2) *
        (finePacketLocalizedUnitCouplingTargetRawWeight
            S leftSource first second pair.1 *
          finePacketLocalizedUnitCouplingTargetRawWeight
            S rightSource first second pair.2) := by
  have hleftFactor :=
    finePacketLocalizedTiltedGibbsRawWeight_eqv_coarseHeatPower_mul_unit
      S leftSource first second pair.1 hleft
  have hrightFactor :=
    finePacketLocalizedTiltedGibbsRawWeight_eqv_coarseHeatPower_mul_unit
      S rightSource first second pair.2 hright
  refine Q'.eqv_trans _
    ((qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.1) *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S leftSource first second pair.1) *
      (qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.2) *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S rightSource first second pair.2)) _
      (qmul_congr_local hleftFactor hrightFactor) ?_
  refine Q'.eqv_trans _
    ((qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.1) *
        qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.2)) *
      (finePacketLocalizedUnitCouplingTargetRawWeight
          S leftSource first second pair.1 *
        finePacketLocalizedUnitCouplingTargetRawWeight
          S rightSource first second pair.2)) _
      (YMGap.Continuum.RingNormaliser.q_mul4_swap _ _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (HeatKernelRGStep.qpow_add S.coarse.coupling
        (slabPhysicalCasimirExponent S.coarse.extent pair.1)
        (slabPhysicalCasimirExponent S.coarse.extent pair.2)))

/-- The exact target-pair heat power before separating its parity ground. -/
theorem finePacketOrientedLocalizedRawPairWeight_eqv_totalCoarseHeatPower_mul_unit
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first second pair) :
    finePacketOrientedLocalizedRawPairWeight
        S orientation first second pair ≈
      qpow S.coarse.coupling
          (slabPhysicalCasimirExponent S.coarse.extent pair.1 +
            slabPhysicalCasimirExponent S.coarse.extent pair.2) *
        finePacketOrientedUnitCouplingTargetRawPairWeight
          S orientation first second pair := by
  have hleft :=
    ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
  have hright :=
    ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
  cases orientation with
  | forward =>
      exact localizedTargetPair_eqv_totalCoarseHeatPower_mul_unit
        S first second first second pair hleft hright
  | reverse =>
      exact localizedTargetPair_eqv_totalCoarseHeatPower_mul_unit
        S second first first second pair hleft hright

/-- The oriented target pair separates exactly into parity-ground heat,
excitation heat, and a coupling-one target reference. -/
theorem finePacketOrientedLocalizedRawPairWeight_eqv_ground_mul_excitation_mul_unit
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedLocalizedRawPairWeight
        S orientation first.1 second.1 pair ≈
      qpow S.coarse.coupling
          (finePacketOrientedTotalTargetParityGroundCasimir
            S orientation first.1 second.1) *
        (qpow S.coarse.coupling
            (finePacketOrientedTotalTargetCasimirExcess
              S orientation first.1 second.1 pair) *
          finePacketOrientedUnitCouplingTargetRawPairWeight
            S orientation first.1 second.1 pair) := by
  have hfactor :=
    finePacketOrientedLocalizedRawPairWeight_eqv_totalCoarseHeatPower_mul_unit
      S orientation first.1 second.1 pair hlowering
  have hdecompose := finePacketOrientedTargetCasimir_exact_decomposition
    S hfineCutoff orientation first second pair hlowering
  refine Q'.eqv_trans _
    (qpow S.coarse.coupling
        (slabPhysicalCasimirExponent S.coarse.extent pair.1 +
          slabPhysicalCasimirExponent S.coarse.extent pair.2) *
      finePacketOrientedUnitCouplingTargetRawPairWeight
        S orientation first.1 second.1 pair) _ hfactor ?_
  rw [hdecompose]
  refine Q'.eqv_trans _
    ((qpow S.coarse.coupling
          (finePacketOrientedTotalTargetParityGroundCasimir
            S orientation first.1 second.1) *
        qpow S.coarse.coupling
          (finePacketOrientedTotalTargetCasimirExcess
            S orientation first.1 second.1 pair)) *
      finePacketOrientedUnitCouplingTargetRawPairWeight
        S orientation first.1 second.1 pair) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (HeatKernelRGStep.qpow_add S.coarse.coupling
        (finePacketOrientedTotalTargetParityGroundCasimir
          S orientation first.1 second.1)
        (finePacketOrientedTotalTargetCasimirExcess
          S orientation first.1 second.1 pair))
  exact Q'.mul_assoc_eqv _ _ _

/-! ## 3. The fine source pair -/

def finePacketFineSourceRawPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling) : Q' :=
  S.fine.physicalTerm first * S.fine.physicalTerm second

def finePacketFineSourceUnitCouplingPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling) : Q' :=
  fineUnitCouplingPhysicalTerm S first *
    fineUnitCouplingPhysicalTerm S second

/-- Both actual fine source masses carry exactly the combined cutoff-one
occupation exponent. -/
theorem finePacketFineSourceRawPairWeight_eqv_occupiedPower_mul_unit
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    finePacketFineSourceRawPairWeight S first.1 second.1 ≈
      qpow S.fine.coupling
          (3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
            fineCouplingPhysicalOccupiedFaceCount S second.1)) *
        finePacketFineSourceUnitCouplingPairWeight
          S first.1 second.1 := by
  have hfirst := fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
    S hfineCutoff first.1 first.2.1
  have hsecond := fineCouplingPhysicalTerm_eqv_occupiedPower_mul_unit
    S hfineCutoff second.1 second.2.1
  unfold finePacketFineSourceRawPairWeight
    finePacketFineSourceUnitCouplingPairWeight
  refine Q'.eqv_trans _
    ((qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S first.1) *
        fineUnitCouplingPhysicalTerm S first.1) *
      (qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S second.1) *
        fineUnitCouplingPhysicalTerm S second.1)) _
      (qmul_congr_local hfirst hsecond) ?_
  refine Q'.eqv_trans _
    ((qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S first.1) *
        qpow S.fine.coupling
          (3 * fineCouplingPhysicalOccupiedFaceCount S second.1)) *
      (fineUnitCouplingPhysicalTerm S first.1 *
        fineUnitCouplingPhysicalTerm S second.1)) _
      (YMGap.Continuum.RingNormaliser.q_mul4_swap _ _ _ _) ?_
  have hexponent :
      3 * fineCouplingPhysicalOccupiedFaceCount S first.1 +
          3 * fineCouplingPhysicalOccupiedFaceCount S second.1 =
        3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
          fineCouplingPhysicalOccupiedFaceCount S second.1) := by
    omega
  rw [← hexponent]
  exact Q'.mul_eqv_congr_right _ _ _
    (Q'.eqv_symm
      (HeatKernelRGStep.qpow_add S.fine.coupling
        (3 * fineCouplingPhysicalOccupiedFaceCount S first.1)
        (3 * fineCouplingPhysicalOccupiedFaceCount S second.1)))

/-! ## 4. Exact suppression times parity-ground reference -/

/-- The actual joint fine-source/coarse-target weight for one oriented
summand. -/
def finePacketOrientedJointGibbsRawPairWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketFineSourceRawPairWeight S first second *
    finePacketOrientedLocalizedRawPairWeight
      S orientation first second pair

/-- The two heat powers which pay joint contour activity.  Both couplings
remain named and may differ. -/
def finePacketOrientedJointSuppressionFactor
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  qpow S.fine.coupling
      (3 * (fineCouplingPhysicalOccupiedFaceCount S first +
        fineCouplingPhysicalOccupiedFaceCount S second)) *
    qpow S.coarse.coupling
      (finePacketOrientedTotalTargetCasimirExcess
        S orientation first second pair)

/-- Everything left after removing joint contour suppression: the exact
coarse parity-ground heat power and the coupling-one fine and coarse finite
weights, including all fusion and link multiplicities. -/
def finePacketOrientedJointParityGroundReferenceWeight
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  qpow S.coarse.coupling
      (finePacketOrientedTotalTargetParityGroundCasimir
        S orientation first second) *
    (finePacketFineSourceUnitCouplingPairWeight S first second *
      finePacketOrientedUnitCouplingTargetRawPairWeight
        S orientation first second pair)

/-- Exact causal factorization of an actual joint summand into the heat
powers controlled by geometric activity and its parity-ground reference.
This is an equality in constructive rationals, not an inequality. -/
theorem finePacketOrientedJointGibbsRawPairWeight_eqv_suppression_mul_reference
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedJointGibbsRawPairWeight
        S orientation first.1 second.1 pair ≈
      finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedJointParityGroundReferenceWeight
          S orientation first.1 second.1 pair := by
  have hsource :=
    finePacketFineSourceRawPairWeight_eqv_occupiedPower_mul_unit
      S hfineCutoff first second
  have htarget :=
    finePacketOrientedLocalizedRawPairWeight_eqv_ground_mul_excitation_mul_unit
      S hfineCutoff orientation first second pair hlowering
  unfold finePacketOrientedJointGibbsRawPairWeight
    finePacketOrientedJointSuppressionFactor
    finePacketOrientedJointParityGroundReferenceWeight
  refine Q'.eqv_trans _
    ((qpow S.fine.coupling
          (3 * (fineCouplingPhysicalOccupiedFaceCount S first.1 +
            fineCouplingPhysicalOccupiedFaceCount S second.1)) *
        finePacketFineSourceUnitCouplingPairWeight S first.1 second.1) *
      (qpow S.coarse.coupling
          (finePacketOrientedTotalTargetParityGroundCasimir
            S orientation first.1 second.1) *
        (qpow S.coarse.coupling
            (finePacketOrientedTotalTargetCasimirExcess
              S orientation first.1 second.1 pair) *
          finePacketOrientedUnitCouplingTargetRawPairWeight
            S orientation first.1 second.1 pair))) _
      (qmul_congr_local hsource htarget) ?_
  ring_qeqv

/-! ## 5. Axiom audit -/

#print axioms finePacketLocalizedUnitCouplingTargetRawWeight
#print axioms finePacketLocalizedTiltedGibbsRawWeight_eqv_coarseHeatPower_mul_unit
#print axioms finePacketOrientedLocalizedRawPairWeight
#print axioms finePacketOrientedUnitCouplingTargetRawPairWeight
#print axioms finePacketOrientedLocalizedRawPairWeight_eqv_totalCoarseHeatPower_mul_unit
#print axioms finePacketOrientedLocalizedRawPairWeight_eqv_ground_mul_excitation_mul_unit
#print axioms finePacketFineSourceRawPairWeight
#print axioms finePacketFineSourceUnitCouplingPairWeight
#print axioms finePacketFineSourceRawPairWeight_eqv_occupiedPower_mul_unit
#print axioms finePacketOrientedJointGibbsRawPairWeight
#print axioms finePacketOrientedJointSuppressionFactor
#print axioms finePacketOrientedJointParityGroundReferenceWeight
#print axioms finePacketOrientedJointGibbsRawPairWeight_eqv_suppression_mul_reference

end YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
