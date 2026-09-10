/-
# Expose the two-scale exterior/core profile in the terminal domination

The normalized common-rate terminal bound is quantitative but its recursive
payments are still opaque to summation.  The existing accepted-state
high-spin profile runs the same canonical recursion while recording, at each
scale, the total exterior multiplicity and the residual low-spin core
multiplicity.  Its pointwise payment is exactly

  anchor^exterior * 2^core.

This module runs that profile on the fine component children and on the
coarse component, proves that its terminal and trace are the canonical ones,
and derives a normalized four-entry bound with all four exponents visible.
The remaining inverse-fiber problem is therefore a concrete summation over
these profiles, rather than an unspecified source-dependent prefactor.

Constructive contract: the established well-founded profiled recursion,
exact rational order, and finite list induction only; no classical choice,
proof hole, trusted external computation, computability escape, heartbeat
increase, or new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
import YMGap.Continuum.Z4DyadicConnectedWitnessRateNormalizedTerminalDomination

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingHighSpinProfile
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
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
open YMGap.Continuum.Z4DyadicConnectedWitnessRateNormalizedTerminalDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
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

/-! ## 1. Profile the same common-rate canonical recursion -/

abbrev FinePacketConnectedFourEntryRateProfiledPeelingOutput
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :=
  SlabAcceptedPairedHighSpinProfileOutput
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0) ×
    SlabAcceptedPairedHighSpinProfileOutput
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateProfiledPeelingOutput
      S rate hrate0 :=
  (slabAcceptedPairCanonicalHighSpinProfile
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 expanded.2.1.1),
    slabAcceptedPairCanonicalHighSpinProfile
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S expanded.2.1)))

/-- At both scales, forgetting the exterior/core counters gives exactly the
canonical terminal and trace already used by the faithful compiler. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling_terminal_trace
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let profiled :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
        S rate hrate0 orientation observableFaceId hobservableFace expanded
    let canonical :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
        S rate hrate0 orientation observableFaceId hobservableFace expanded
    (profiled.1.1, profiled.1.2.1) = canonical.1 ∧
      (profiled.2.1, profiled.2.2.1) = canonical.2 := by
  constructor
  · exact slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 expanded.2.1.1)
  · exact slabAcceptedPairCanonicalHighSpinProfile_terminal_trace
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S expanded.2.1))

/-! ## 2. The four explicit profile exponents -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateProfilePayment
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
      (Q'.ofNat 2) ^ result.1.2.2.2) *
    (anchorFaceCoefficient ^ result.2.2.2.1 *
      (Q'.ofNat 2) ^ result.2.2.2.2)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateProfileTerminalBudget
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let result :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  finePacketGlobalNonzeroConnectedExpandedWitnessRateProfilePayment
      S rate hrate0 orientation observableFaceId hobservableFace expanded *
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        result.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        result.2.1)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  Q'.divPos
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateProfileTerminalBudget
      S rate hrate0 orientation observableFaceId hobservableFace expanded)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

/-! ## 3. Pointwise profiled domination -/

private theorem finePacketOrientedJointExpandedWitnessAtCouplingWeight_le_profileTerminalBudget
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
      finePacketGlobalNonzeroConnectedExpandedWitnessRateProfileTerminalBudget
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
    (Q'.ofNat 2) ^ fineResult.2.2.2
  let coarseCoefficient := anchorFaceCoefficient ^ coarseResult.2.2.1 *
    (Q'.ofNat 2) ^ coarseResult.2.2.2
  have hfine := slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
    fineD
    (by simpa only [fineD, finePacketFineRateCouplingSlabPhysicalData,
      slabPhysicalDataAtCoupling] using hrate0)
    (by simpa only [fineD, finePacketFineRateCouplingSlabPhysicalData,
      slabPhysicalDataAtCoupling] using hrate1)
    fineFaces finePhysical fineState
  have hcoarse := slabAcceptedPairCanonicalHighSpinProfile_sourceWeight_le
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
        (Q'.pow_nonneg (Q'.ofNat 2) (by decide) fineResult.2.2.2))
      (slabAcceptedTwoReplicaStateWeight_nonnegative fineD fineResult.1)
  have hcoarseSource0 : (0 : Q') ≤
      slabAcceptedTwoReplicaStateWeight coarseD coarseState :=
    slabAcceptedTwoReplicaStateWeight_nonnegative coarseD coarseState
  have hproduct := Q'.mul_le_mul_of_nonneg hfine hcoarse
    hfineUpper0 hcoarseSource0
  unfold finePacketOrientedJointExpandedWitnessAtCouplingWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfileTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateProfilePayment
  change slabAcceptedTwoReplicaStateWeight fineD fineState *
      slabAcceptedTwoReplicaStateWeight coarseD coarseState ≤ _
  exact Q'.le_trans' _ _ _ hproduct
    (Q'.le_of_eqv (mul_four_regroup_local _ _ _ _))

/-- The actual normalized connected weight is bounded by the four-exponent
profiled terminal budget.  The beta/rate interval remains explicit. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedProfileTerminalBudget
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
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudget
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
    finePacketOrientedJointExpandedWitnessAtCouplingWeight_le_profileTerminalBudget
      S rate hrate0 hrate1 orientation observableFaceId
        hobservableFace expanded
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos normalization hnormalization) hprofile
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))
  refine Q'.le_trans' _ _ _ hdom ?_
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudget
    Q'.divPos
  simpa only [rate0, normalization] using hscaled

/-! ## 4. The aggregate frontier in profiled form -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudget
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

theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedProfileTerminalBudgetMass
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
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudgetMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudgetMass
  apply listQSum_le_termwise_local
  intro expanded _
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedProfileTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        orientation observableFaceId hobservableFace expanded

#print axioms FinePacketConnectedFourEntryRateProfiledPeelingOutput
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfiledPeeling_terminal_trace
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfilePayment
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedProfileTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedProfileTerminalBudgetMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedProfileTerminalBudgetMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateProfiledTerminalDomination
