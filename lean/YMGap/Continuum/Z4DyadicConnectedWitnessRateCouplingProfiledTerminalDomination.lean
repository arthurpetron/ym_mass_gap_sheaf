/-
# Coupling-sharp two-scale profiled terminal domination

The first profiled four-entry bound used the generic residual-core ceiling
`2^core`.  The literal SU(2) heat coefficient is sharper: every residual-core
copy pays `exteriorFaceCoefficient rate 0 = 2 * rate^3`.  This module threads
that exact beta/rate dependence through both the fine and coarse profiled
peelings and through the existing positive normalization.

The result is the correct analytic interface for the next inverse-fiber
summation.  It neither calls the rate uniform nor assumes that the residual
coefficient is contractive; any strong-coupling corridor or RG entry theorem
must supply that comparison explicitly.

Constructive contract: exact SU(2) heat-coefficient comparison, established
well-founded peeling, guarded rational division, and finite list induction
only; no classical choice, proof hole, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingWeight
import YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfiledTerminalDomination

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
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
open YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. Exact coupling-sensitive payment -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  (anchorFaceCoefficient ^ result.1.2.2.1 *
      exteriorFaceCoefficient rate 0 ^ result.1.2.2.2) *
    (anchorFaceCoefficient ^ result.2.2.2.1 *
      exteriorFaceCoefficient rate 0 ^ result.2.2.2.2)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
      S rate hrate0 orientation observableFaceId hobservableFace expanded *
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        result.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        result.2.1)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  Q'.divPos
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
      S rate hrate0 orientation observableFaceId hobservableFace expanded)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

/-! ## 2. Four-entry source telescope with `2 * rate^3` in the core -/

private theorem finePacketOrientedJointExpandedWitnessAtCouplingWeight_le_couplingProfileTerminalBudget
    (S : SlabScalePair) (rate : Q')
    (hrate0 : (0 : Q') < rate) (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketOrientedJointExpandedWitnessAtCouplingWeight
        S rate rate0 expanded.2.1 ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
        S rate rate0 orientation observableFaceId hobservableFace expanded := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  let fineD := finePacketFineRateCouplingSlabPhysicalData S rate rate0
  let coarseD := finePacketCoarseRateCouplingSlabPhysicalData S rate rate0
  let fineFaces := finePacketGlobalNonzeroConnectedEntryFineComponentFaces
    S orientation observableFaceId expanded.1
  let coarseFaces := finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
    S orientation observableFaceId expanded.1
  let finePhysical :=
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate rate0 orientation observableFaceId hobservableFace expanded.1
  let coarsePhysical :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate rate0 orientation observableFaceId hobservableFace expanded.1
  let fineState := slabAcceptedTwoReplicaStateAtCoupling
    (finePacketFineUnitCouplingSlabPhysicalData S)
    rate rate0 expanded.2.1.1
  let coarseState := slabAcceptedTwoReplicaStateAtCoupling
    (coarseUnitCouplingSlabPhysicalData S)
    rate rate0
    (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S expanded.2.1)
  let fineResult := slabAcceptedPairCanonicalHighSpinProfile
    fineD (anchorPaidExteriorThreshold rate)
      fineFaces finePhysical fineState
  let coarseResult := slabAcceptedPairCanonicalHighSpinProfile
    coarseD (anchorPaidExteriorThreshold rate)
      coarseFaces coarsePhysical coarseState
  let fineCoefficient := anchorFaceCoefficient ^ fineResult.2.2.1 *
    exteriorFaceCoefficient rate 0 ^ fineResult.2.2.2
  let coarseCoefficient := anchorFaceCoefficient ^ coarseResult.2.2.1 *
    exteriorFaceCoefficient rate 0 ^ coarseResult.2.2.2
  have hfine :=
    slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
      fineD
      (by simpa only [fineD, finePacketFineRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate0)
      (by simpa only [fineD, finePacketFineRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate1)
      fineFaces finePhysical fineState
  have hcoarse :=
    slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le_zeroCoefficient
      coarseD
      (by simpa only [coarseD, finePacketCoarseRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate0)
      (by simpa only [coarseD, finePacketCoarseRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate1)
      coarseFaces coarsePhysical coarseState
  have hfineUpper0 : (0 : Q') ≤
      fineCoefficient * slabAcceptedTwoReplicaStateWeight fineD fineResult.1 :=
    Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorFaceCoefficient (by decide) fineResult.2.2.1)
        (Q'.pow_nonneg (exteriorFaceCoefficient rate 0)
          (exteriorFaceCoefficient_nonnegative rate0 0)
          fineResult.2.2.2))
      (slabAcceptedTwoReplicaStateWeight_nonnegative fineD fineResult.1)
  have hcoarseSource0 : (0 : Q') ≤
      slabAcceptedTwoReplicaStateWeight coarseD coarseState :=
    slabAcceptedTwoReplicaStateWeight_nonnegative coarseD coarseState
  have hproduct := Q'.mul_le_mul_of_nonneg hfine hcoarse
    hfineUpper0 hcoarseSource0
  unfold finePacketOrientedJointExpandedWitnessAtCouplingWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
  change slabAcceptedTwoReplicaStateWeight fineD fineState *
      slabAcceptedTwoReplicaStateWeight coarseD coarseState ≤ _
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv (mul_four_regroup_local _ _ _ _))

/-- **Coupling-sharp pointwise normalized terminal domination.**  The core
coefficient is displayed as `2 * rate^3`; no beta-uniform claim is made. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedCouplingProfileTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace expanded := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  let normalization := finePacketOrientedEnvelopeNormalizationMass S
    expanded.1.1.sources.1 expanded.1.1.sources.2
  have hnormalization : (0 : Q') < normalization :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2
  have hdom :=
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateCoupled
      S hfineCutoff hcoarseCoupling rate rate0 hcoarseRate orientation
        observableFaceId hobservableFace expanded
  have hprofile :=
    finePacketOrientedJointExpandedWitnessAtCouplingWeight_le_couplingProfileTerminalBudget
      S rate hrate0 hrate1 orientation observableFaceId
        hobservableFace expanded
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos normalization hnormalization) hprofile
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))
  refine Q'.le_trans' _ _ _ hdom ?_
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
    Q'.divPos
  simpa only [rate0, normalization] using hscaled

/-! ## 3. Aggregate coupling-sharp frontier -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 orientation
        observableFaceId hobservableFace)
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

theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedCouplingProfileTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudgetMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudgetMass
  apply listQSum_le_termwise_local
  intro expanded _
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedCouplingProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        orientation observableFaceId hobservableFace expanded

#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfilePayment
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCouplingProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedCouplingProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedCouplingProfileTerminalBudgetMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedCouplingProfileTerminalBudgetMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateCouplingProfiledTerminalDomination
