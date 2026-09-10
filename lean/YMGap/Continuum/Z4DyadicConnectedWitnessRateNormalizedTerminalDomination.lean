/-
# Normalize the common-rate terminal telescope

The common-rate Casimir comparison bounds the actual connected expanded
witness by a normalized four-state weight.  The synchronized fine/coarse
peelings bound that four-state numerator by their explicit path payments
times the two actual terminal weights.  Since both statements use the same
positive two-row normalization, they compose without any new constant.

The resulting pointwise theorem is summed over the literal flattened
connected-witness carrier.  Its right side is the precise terminal budget
which the next inverse-fiber argument must contract; in particular, neither
the source-dependent payments nor the normalization are hidden in an opaque
"uniform" constant.

Constructive contract: exact rational order, positive guarded division, and
finite list induction only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateNormalizedTerminalDomination

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination
open YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
open YMGap.Continuum.Z4DyadicConnectedWitnessRateTerminalCompilerFaithfulness
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. The literal terminal-side numerator and normalization -/

/-- Fine payment times coarse payment times the two synchronized terminal
weights.  Every dependence on the comparison rate and source is explicit. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  let weighted :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  let canonical :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  (weighted.1.2 * weighted.2.2) *
    (slabAcceptedTwoReplicaStateWeight
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        canonical.1.1 *
      slabAcceptedTwoReplicaStateWeight
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        canonical.2.1)

/-- The terminal budget divided by the same exact two-row normalization used
by the connected expanded-witness weight. -/
def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  Q'.divPos
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
      S rate hrate0 orientation observableFaceId hobservableFace expanded)
    (finePacketOrientedEnvelopeNormalizationMass S
      expanded.1.1.sources.1 expanded.1.1.sources.2)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2)

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget_nonnegative
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (0 : Q') ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
        S rate hrate0 orientation observableFaceId hobservableFace expanded := by
  let weighted :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  let canonical :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
      S rate hrate0 orientation observableFaceId hobservableFace expanded
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        (anchorPaidExteriorThreshold rate)
        (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
          S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
        (YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase.slabAcceptedTwoReplicaStateAtCoupling
          (YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness.finePacketFineUnitCouplingSlabPhysicalData S)
          rate hrate0 expanded.2.1.1))
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        (anchorPaidExteriorThreshold rate)
        (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
          S orientation observableFaceId expanded.1)
        (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
          S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
        (YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase.slabAcceptedTwoReplicaStateAtCoupling
          (YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness.coarseUnitCouplingSlabPhysicalData S)
          rate hrate0
          (YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling.finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
            S expanded.2.1))))
    (Q'.mul_nonneg _ _
      (slabAcceptedTwoReplicaStateWeight_nonnegative
        (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
        canonical.1.1)
      (slabAcceptedTwoReplicaStateWeight_nonnegative
        (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
        canonical.2.1))

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    (0 : Q') ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
        S hfineCutoff hcoarseCoupling rate hrate0 orientation
          observableFaceId hobservableFace expanded := by
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
    Q'.divPos
  exact Q'.mul_nonneg _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget_nonnegative
      S rate hrate0 orientation observableFaceId hobservableFace expanded)
    (Q'.le_of_lt (Q'.recipPos_pos _
      (finePacketOrientedEnvelopeNormalizationMass_pos
        S hfineCutoff hcoarseCoupling
          expanded.1.1.sources.1 expanded.1.1.sources.2)))

/-! ## 2. The actual connected weight lands on that terminal budget -/

/-- Dividing the synchronized raw telescope by the exact positive envelope
normalization preserves its order. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight_le_terminalBudget
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') < rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId expanded ≤
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace expanded := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  let normalization := finePacketOrientedEnvelopeNormalizationMass S
    expanded.1.1.sources.1 expanded.1.1.sources.2
  have hnormalization : (0 : Q') < normalization :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling
        expanded.1.1.sources.1 expanded.1.1.sources.2
  have htelescope :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling_sourceWeight_le
      S rate hrate0 hrate1 orientation observableFaceId
        hobservableFace expanded
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (Q'.recipPos normalization hnormalization) htelescope
    (Q'.le_of_lt (Q'.recipPos_pos normalization hnormalization))
  unfold
    finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
    finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
    Q'.divPos
  simpa only [rate0, normalization] using hscaled

/-- **Pointwise normalized terminal domination.**  The actual connected
expanded-witness weight is bounded by the explicit common-rate fine/coarse
payment and terminal budget.  The permitted rate interval and the comparison
with the physical coarse coupling are named in the statement. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedTerminalBudget
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
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace expanded := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateCoupled
      S hfineCutoff hcoarseCoupling rate rate0 hcoarseRate orientation
        observableFaceId hobservableFace expanded)
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight_le_terminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 orientation
        observableFaceId hobservableFace expanded)

/-! ## 3. Sum the pointwise theorem over the exact flattened carrier -/

def finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudgetMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
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

/-- The complete connected expanded-witness mass is reduced to the explicit
sum of normalized synchronized terminal budgets. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedTerminalBudgetMass
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
      finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudgetMass
        S hfineCutoff hcoarseCoupling rate rate0 orientation
          observableFaceId hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudgetMass
  apply listQSum_le_termwise_local
  intro expanded _
  exact
    finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedTerminalBudget
      S hfineCutoff hcoarseCoupling rate hrate0 hrate1 hcoarseRate
        orientation observableFaceId hobservableFace expanded

#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateTerminalBudget_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudget_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCoupledNormalizedWeight_le_terminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight_le_rateNormalizedTerminalBudget
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateNormalizedTerminalBudgetMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_le_rateNormalizedTerminalBudgetMass

end YMGap.Continuum.Z4DyadicConnectedWitnessRateNormalizedTerminalDomination
