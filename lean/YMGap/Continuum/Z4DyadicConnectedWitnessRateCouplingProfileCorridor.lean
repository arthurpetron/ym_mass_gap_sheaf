/-
# Collapse the two-scale coupling profile on the proved corridor

The coupling-sharp four-entry telescope pays

  anchor^exterior * (2 * rate^3)^core

at each of the fine and coarse scales.  This module proves the exact causal
next step: if the residual coefficient is below the anchor coefficient, all
four visible counters collapse to one anchor power.  The existing SU(2)
coefficient calculation supplies that premise whenever `rate <= 1/400`.

The result is stated first behind the coefficient premise and then on the
explicit strong-coupling corridor.  It does not claim that a bare continuum
coupling lies in that corridor; an RG-entry or non-abelian coercivity theorem
must still establish such an input before this contraction can contribute to
a continuum mass gap.

Constructive contract: exact rational coefficient comparisons, established
SU(2) peeling, positive guarded division, and finite list induction only; no
classical choice, proof hole, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor
import YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfiledTerminalDomination

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. One complete two-scale profile mass -/

/-- Fine exterior, fine core, coarse exterior, and coarse core multiplicities,
added without dropping either scale. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Nat :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  (result.1.2.2.1 + result.1.2.2.2) +
    (result.2.2.2.1 + result.2.2.2.2)

/-! ## 2. Collapse the exact profile payment to one anchor power -/

/-- Assumption-level collapse.  This is the interface to be supplied by an
RG-entry or non-abelian local-coercivity theorem outside the proved corridor. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower_of_zeroCoefficient_le
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (hzero : exteriorFaceCoefficient rate 0 ≤ anchorFaceCoefficient)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
        S rate hrate0 orientation observableFaceId hobservableFace expanded ≤
      anchorFaceCoefficient ^
        finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
          S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  have hfine :=
    highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
      hrate0 hzero result.1.2.2.1 result.1.2.2.2
  have hcoarse :=
    highSpinProfileCoefficient_le_anchorPower_of_zeroCoefficient_le
      hrate0 hzero result.2.2.2.1 result.2.2.2.2
  have hfineAnchor0 : (0 : Q') ≤
      anchorFaceCoefficient ^ (result.1.2.2.1 + result.1.2.2.2) :=
    Q'.pow_nonneg anchorFaceCoefficient (by decide) _
  have hcoarseCoefficient0 : (0 : Q') ≤
      anchorFaceCoefficient ^ result.2.2.2.1 *
        exteriorFaceCoefficient rate 0 ^ result.2.2.2.2 :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorFaceCoefficient (by decide) _)
      (Q'.pow_nonneg (exteriorFaceCoefficient rate 0)
        (exteriorFaceCoefficient_nonnegative hrate0 0) _)
  have hproduct := Q'.mul_le_mul_of_nonneg hfine hcoarse
    hfineAnchor0 hcoarseCoefficient0
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
    finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
  change
    (anchorFaceCoefficient ^ result.1.2.2.1 *
        exteriorFaceCoefficient rate 0 ^ result.1.2.2.2) *
      (anchorFaceCoefficient ^ result.2.2.2.1 *
        exteriorFaceCoefficient rate 0 ^ result.2.2.2.2) ≤
      anchorFaceCoefficient ^
        ((result.1.2.2.1 + result.1.2.2.2) +
          (result.2.2.2.1 + result.2.2.2.2))
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.pow_add_eqv anchorFaceCoefficient
          (result.1.2.2.1 + result.1.2.2.2)
          (result.2.2.2.1 + result.2.2.2.2))))

/-- On the explicit SU(2) corridor `rate <= 1/400`, the exact residual
coefficient premise follows from its formula `2 * rate^3`. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
        S rate hrate0 orientation observableFaceId hobservableFace expanded ≤
      anchorFaceCoefficient ^
        finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
          S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower_of_zeroCoefficient_le
      S rate hrate0
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          hrate0 hrateAnchor)
        orientation observableFaceId hobservableFace expanded

/-! ## 3. Anchor-power terminal budgets -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  anchorFaceCoefficient ^
      finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
        S rate hrate0 orientation observableFaceId hobservableFace expanded *
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        result.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        result.2.1)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  Q'.divPos
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
      S rate hrate0 orientation observableFaceId hobservableFace expanded)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

private theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget_le_anchorProfileTerminalBudget_of_zeroCoefficient_le
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (hzero : exteriorFaceCoefficient rate 0 ≤ anchorFaceCoefficient)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
        S rate hrate0 orientation observableFaceId hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
        S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  have hpayment :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower_of_zeroCoefficient_le
      S rate hrate0 hzero orientation observableFaceId hobservableFace expanded
  have hterminal0 : (0 : Q') ≤
      slabAcceptedTwoReplicaStateWeight
          (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
          result.1.1 *
        slabAcceptedTwoReplicaStateWeight
          (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
          result.2.1 :=
    Q'.mul_nonneg _ _
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ _)
      (slabAcceptedTwoReplicaStateWeight_nonnegative _ _)
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hpayment hterminal0

private theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget_le_normalizedAnchorProfileTerminalBudget_of_zeroCoefficient_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (hzero : exteriorFaceCoefficient rate 0 ≤ anchorFaceCoefficient)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
          hobservableFace expanded := by
  let normalization := finePacketOrientedEnvelopeNormalizationMass S
    expanded.1.1.sources.1 expanded.1.1.sources.2
  have hnormalization : (0 : Q') < normalization :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2
  have hbudget :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget_le_anchorProfileTerminalBudget_of_zeroCoefficient_le
      S rate hrate0 hzero orientation observableFaceId hobservableFace expanded
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos normalization hnormalization) hbudget
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
    Q'.divPos
  simpa only [normalization] using hscaled

/-! ## 4. Pointwise and aggregate corridor contraction -/

/-- Pointwise anchor-power domination behind the exact residual-coefficient
premise.  All dependence on the rate and on both scales remains in the type. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget_of_zeroCoefficient_le
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hzero : exteriorFaceCoefficient rate 0 ≤ anchorFaceCoefficient)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace expanded := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  have hcoupling :=
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedCouplingProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate orientation
        observableFaceId hobservableFace expanded
  have hcollapse :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget_le_normalizedAnchorProfileTerminalBudget_of_zeroCoefficient_le
      S hfineCutoff hcoarseCoupling rate rate0 hzero orientation
        observableFaceId hobservableFace expanded
  exact Q'.le_trans' _ _ _ hcoupling hcollapse

/-- Explicit strong-coupling specialization.  This theorem requires and names
`rate <= anchorCoupling`; it contains no beta-uniform claim. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace expanded := by
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget_of_zeroCoefficient_le
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hrate0) hrateAnchor)
        orientation observableFaceId hobservableFace expanded

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 orientation observableFaceId
        hobservableFace)
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-- Aggregate four-entry connected witness mass in the explicit SU(2)
strong-coupling corridor. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedAnchorProfileTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrateAnchor : rate ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
  apply listQSum_le_termwise_local
  intro expanded _
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate hrateAnchor
        orientation observableFaceId hobservableFace expanded

#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateTotalProfileMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower_of_zeroCoefficient_le
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment_le_anchorPower
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateAnchorProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget_of_zeroCoefficient_le
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedAnchorProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedAnchorProfileTerminalBudgetMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedAnchorProfileTerminalBudgetMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfileCorridor
