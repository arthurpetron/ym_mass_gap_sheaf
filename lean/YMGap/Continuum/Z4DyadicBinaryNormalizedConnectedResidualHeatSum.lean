/-
# The normalized connected sum with residual heat retained

Milestone 333 repaired the pointwise distance extraction by preserving the
common-rate heat power left after the geometric floor is paid.  This module
threads that stronger inequality through the exact tilted-row normalization
and the complete attached connected target-pair carrier.

For every positive pair of fine sources and either envelope orientation,

`normalized connected joint mass`
`  <= sum_connected`
`       (rate^3)^(distance + 1) * rate^residual * unitCongestion`.

The residual factor is part of the summand and remains available for later
component/exterior normalization.  No estimate of that finite sum or its
volume dependence is asserted.

Constructive contract: explicit finite sums, checked lowering/path witnesses,
and positivity-guarded rational arithmetic only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
import YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression

namespace YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedResidualHeatSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
open YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion
open YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedGeometry
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

/-! ## 1. The residual-heat congestion summand -/

/-- Coupling-one congestion with every common-rate heat unit not spent on
distance restored. -/
def finePacketOrientedConnectedResidualHeatUnitCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : {pair // pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId}) : Q' :=
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace entry.1 entry.2
  qpow rate
      (finePacketOrientedConnectedResidualHeatExponent
        S orientation first.1 second.1 observableFaceId entry.1 path) *
    finePacketOrientedJointUnitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second entry.1

/-- The complete refined summand: geometric distance decay times the retained
residual-heat congestion. -/
def finePacketOrientedConnectedDistanceResidualHeatCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : {pair // pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId}) : Q' :=
  let path := finePacketFaceResponseConnectedActivePairPath
    S first.1 second.1 observableFaceId hobservableFace entry.1 entry.2
  qpow (finePacketJointDistanceFugacity rate)
      (linfDist
        (slabPlaquetteAt S.coarse.extent observableFaceId)
        (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) *
    finePacketOrientedConnectedResidualHeatUnitCongestion
      S hfineCutoff hcoarseCoupling rate orientation first second
        observableFaceId hobservableFace entry

/-! ## 2. Refined pointwise normalized bound -/

theorem finePacketOrientedNormalizedJointPairWeight_le_distanceResidualHeatCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair)
    (path : FinePacketObservableConnectedDisagreementPath
      S first.1 second.1 observableFaceId pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      qpow (finePacketJointDistanceFugacity rate)
          (linfDist
            (slabPlaquetteAt S.coarse.extent observableFaceId)
            (slabPlaquetteAt S.coarse.extent path.sourceFaceId) + 1) *
        (qpow rate
            (finePacketOrientedConnectedResidualHeatExponent
              S orientation first.1 second.1 observableFaceId pair path) *
          finePacketOrientedJointUnitReferenceCongestion
            S hfineCutoff hcoarseCoupling orientation first second pair) := by
  have hnormalized :=
    finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_unitCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  have hsuppression :=
    finePacketOrientedConnectedPath_jointSuppression_le_distance_mul_residual
      S hfineCutoff rate hfineRate hcoarseRate orientation first second
        observableFaceId hobservableFace pair hlowering path
  have hunit0 := finePacketOrientedJointUnitReferenceCongestion_nonnegative
    S hfineCutoff hcoarseCoupling orientation first second pair
  refine Q'.le_trans' _ _ _ hnormalized
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hsuppression hunit0) ?_)
  exact Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)

private theorem finePacketOrientedNormalizedJointPairWeight_le_connectedResidualWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      finePacketOrientedConnectedDistanceResidualHeatCongestion
        S hfineCutoff hcoarseCoupling rate orientation first second
          observableFaceId hobservableFace ⟨pair, hpair⟩ := by
  by_cases hzero : finePacketOrientedLocalizedRawPairWeight
      S orientation first.1 second.1 pair ≈ 0
  · have hnormalized :=
      finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
        S hfineCutoff hcoarseCoupling orientation first second pair hzero
    have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
      S.fine.coupling_nonnegative hfineRate
    unfold finePacketOrientedConnectedDistanceResidualHeatCongestion
      finePacketOrientedConnectedResidualHeatUnitCongestion
    dsimp only
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalized)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _ (qpow_nonneg rate hrate0 3) _)
        (Q'.mul_nonneg _ _
          (qpow_nonneg rate hrate0 _)
          (finePacketOrientedJointUnitReferenceCongestion_nonnegative
            S hfineCutoff hcoarseCoupling orientation first second pair)))
  · have hactive := (List.mem_filter.mp hpair).1
    have hphysical := (List.mem_filter.mp hactive).1
    have hlowering : finePacketOrientedLoweringPair
        S orientation first.1 second.1 pair := by
      cases orientation with
      | forward =>
          exact finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
            S hfineCutoff first second pair hphysical hzero
      | reverse =>
          exact finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
            S hfineCutoff first second pair hphysical hzero
    have hbound :=
      finePacketOrientedNormalizedJointPairWeight_le_distanceResidualHeatCongestion
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
          orientation first second observableFaceId hobservableFace pair
          hlowering
          (finePacketFaceResponseConnectedActivePairPath
            S first.1 second.1 observableFaceId hobservableFace pair hpair)
    unfold finePacketOrientedConnectedDistanceResidualHeatCongestion
      finePacketOrientedConnectedResidualHeatUnitCongestion
    simpa only using hbound

/-! ## 3. Sum the proof-carrying connected carrier -/

def finePacketOrientedConnectedDistanceResidualHeatCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketOrientedConnectedDistanceResidualHeatCongestion
      S hfineCutoff hcoarseCoupling rate orientation first second
        observableFaceId hobservableFace)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId).attach

/-- The exact normalized connected carrier is bounded without erasing the
residual heat needed to control exterior multiplicity. -/
theorem finePacketOrientedNormalizedConnectedJointMass_le_distanceResidualHeatCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≤
      finePacketOrientedConnectedDistanceResidualHeatCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation first second
          observableFaceId hobservableFace := by
  unfold finePacketOrientedNormalizedConnectedJointMass
    finePacketOrientedConnectedDistanceResidualHeatCongestionMass
  apply listQSum_mono_local
  intro entry _hentry
  exact
    finePacketOrientedNormalizedJointPairWeight_le_connectedResidualWeight
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
        orientation first second observableFaceId hobservableFace
        entry.1 entry.2

/-! ## 4. Axiom audit -/

#print axioms finePacketOrientedConnectedResidualHeatUnitCongestion
#print axioms finePacketOrientedConnectedDistanceResidualHeatCongestion
#print axioms finePacketOrientedNormalizedJointPairWeight_le_distanceResidualHeatCongestion
#print axioms finePacketOrientedConnectedDistanceResidualHeatCongestionMass
#print axioms finePacketOrientedNormalizedConnectedJointMass_le_distanceResidualHeatCongestionMass

end YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedResidualHeatSum
