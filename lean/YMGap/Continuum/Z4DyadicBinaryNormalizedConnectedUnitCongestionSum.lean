/-
# The normalized connected response as a distance-weighted unit congestion sum

For a fixed positive pair of fine sources, divide each actual oriented joint
source-target summand by the exact product of its two tilted-row masses.  The
parity-ground normalization theorem bounds this quotient by heat suppression
times reference congestion, and the heat-free cancellation theorem replaces
that congestion by an explicit coupling-one expression.

On the connected active carrier, zero raw orientations contribute exactly
zero.  Every nonzero orientation supplies its checked lowering pair and
observable-rooted disagreement path, so the subunit heat theorem inserts one
`rate^3` factor per unit of distance plus one.  Summation gives the exact next
analytic interface:

`normalized connected joint mass`
`  <= sum_connected distancePower * unitReferenceCongestion`.

No estimate on the remaining finite sum or its volume dependence is asserted.

Constructive contract: explicit finite sums, positivity-guarded rational
division, and checked path witnesses only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion

namespace YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum

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
open YMGap.Continuum.Z4DyadicBinaryJointParityGroundNormalization
open YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion
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

private theorem mul_eqv_zero_of_right_local
    (left right : Q') (hright : right ≈ 0) :
    left * right ≈ 0 := by
  refine Q'.eqv_trans _ (left * 0) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ hright
  · exact Q'.mul_zero_eqv left

/-! ## 1. Normalize one actual joint summand by its two target-row masses -/

def finePacketOrientedNormalizedJointPairWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  Q'.divPos
    (finePacketOrientedJointGibbsRawPairWeight
      S orientation first.1 second.1 pair)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

theorem finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_congestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedJointReferenceCongestionRatio
          S hfineCutoff hcoarseCoupling orientation first second pair := by
  unfold finePacketOrientedNormalizedJointPairWeight
  apply Q'.divPos_le_of_le_mul
  exact
    finePacketOrientedJointGibbsRawPairWeight_le_suppression_mul_congestion_mul_rowNormalization
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering

theorem finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_unitCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedJointUnitReferenceCongestion
          S hfineCutoff hcoarseCoupling orientation first second pair := by
  have hbound :=
    finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_congestion
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  have hcongestion :=
    finePacketOrientedJointReferenceCongestionRatio_eqv_unitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair
  exact Q'.le_trans' _ _ _ hbound
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        (finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair) _ _ hcongestion))

theorem finePacketOrientedJointUnitReferenceCongestion_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedJointUnitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair := by
  have hold :=
    finePacketOrientedJointReferenceCongestionRatio_nonnegative
      S hfineCutoff hcoarseCoupling orientation first second pair
  have heq :=
    finePacketOrientedJointReferenceCongestionRatio_eqv_unitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair
  exact Q'.le_trans' _ _ _ hold (Q'.le_of_eqv heq)

/-! ## 2. Insert the connected-path distance power -/

def finePacketOrientedConnectedDistanceWeightedUnitCongestion
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
    finePacketOrientedJointUnitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second entry.1

theorem finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hzero : finePacketOrientedLocalizedRawPairWeight
      S orientation first.1 second.1 pair ≈ 0) :
    finePacketOrientedNormalizedJointPairWeight
      S hfineCutoff hcoarseCoupling orientation first second pair ≈ 0 := by
  have hjoint : finePacketOrientedJointGibbsRawPairWeight
      S orientation first.1 second.1 pair ≈ 0 := by
    unfold finePacketOrientedJointGibbsRawPairWeight
    exact mul_eqv_zero_of_right_local _ _ hzero
  unfold finePacketOrientedNormalizedJointPairWeight Q'.divPos
  refine Q'.eqv_trans _ (0 * Q'.recipPos
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ hjoint
  · exact Q'.zero_mul_eqv _

theorem finePacketOrientedNormalizedJointPairWeight_le_distanceWeightedUnitCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
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
        finePacketOrientedJointUnitReferenceCongestion
          S hfineCutoff hcoarseCoupling orientation first second pair := by
  have hnormalized :=
    finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_unitCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  have hsuppression :=
    finePacketOrientedConnectedPath_jointSuppression_le_distanceFugacity
      S hfineCutoff rate hfineRate hcoarseRate hrate1 orientation
      first second observableFaceId hobservableFace pair hlowering path
  have hunit0 := finePacketOrientedJointUnitReferenceCongestion_nonnegative
    S hfineCutoff hcoarseCoupling orientation first second pair
  exact Q'.le_trans' _ _ _ hnormalized
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hsuppression hunit0)

private theorem finePacketForwardNormalizedJointPairWeight_le_connectedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling .forward first second pair ≤
      finePacketOrientedConnectedDistanceWeightedUnitCongestion
        S hfineCutoff hcoarseCoupling rate .forward first second
          observableFaceId hobservableFace ⟨pair, hpair⟩ := by
  by_cases hzero : finePacketForwardLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0
  · have hnormalized :=
      finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
        S hfineCutoff hcoarseCoupling .forward first second pair hzero
    have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
      S.fine.coupling_nonnegative hfineRate
    unfold finePacketOrientedConnectedDistanceWeightedUnitCongestion
    dsimp only
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalized)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _
          (qpow_nonneg rate hrate0 3) _)
        (finePacketOrientedJointUnitReferenceCongestion_nonnegative
          S hfineCutoff hcoarseCoupling .forward first second pair))
  · have hactive := (List.mem_filter.mp hpair).1
    have hphysical := (List.mem_filter.mp hactive).1
    have hlowering :=
      finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
        S hfineCutoff first second pair hphysical hzero
    have hbound :=
      finePacketOrientedNormalizedJointPairWeight_le_distanceWeightedUnitCongestion
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate hrate1
          .forward first second observableFaceId hobservableFace pair
          hlowering
          (finePacketFaceResponseConnectedActivePairPath
            S first.1 second.1 observableFaceId hobservableFace pair hpair)
    unfold finePacketOrientedConnectedDistanceWeightedUnitCongestion
    simpa only using hbound

private theorem finePacketReverseNormalizedJointPairWeight_le_connectedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling .reverse first second pair ≤
      finePacketOrientedConnectedDistanceWeightedUnitCongestion
        S hfineCutoff hcoarseCoupling rate .reverse first second
          observableFaceId hobservableFace ⟨pair, hpair⟩ := by
  by_cases hzero : finePacketReverseLocalizedRawPairWeight
      S first.1 second.1 pair ≈ 0
  · have hnormalized :=
      finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
        S hfineCutoff hcoarseCoupling .reverse first second pair hzero
    have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
      S.fine.coupling_nonnegative hfineRate
    unfold finePacketOrientedConnectedDistanceWeightedUnitCongestion
    dsimp only
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalized)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _
          (qpow_nonneg rate hrate0 3) _)
        (finePacketOrientedJointUnitReferenceCongestion_nonnegative
          S hfineCutoff hcoarseCoupling .reverse first second pair))
  · have hactive := (List.mem_filter.mp hpair).1
    have hphysical := (List.mem_filter.mp hactive).1
    have hlowering :=
      finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
        S hfineCutoff first second pair hphysical hzero
    have hbound :=
      finePacketOrientedNormalizedJointPairWeight_le_distanceWeightedUnitCongestion
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate hrate1
          .reverse first second observableFaceId hobservableFace pair
          hlowering
          (finePacketFaceResponseConnectedActivePairPath
            S first.1 second.1 observableFaceId hobservableFace pair hpair)
    unfold finePacketOrientedConnectedDistanceWeightedUnitCongestion
    simpa only using hbound

/-! ## 3. Sum the exact connected carrier -/

def finePacketOrientedNormalizedConnectedJointMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun entry : {pair // pair ∈ finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId} =>
      finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second entry.1)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId).attach

def finePacketOrientedConnectedDistanceWeightedUnitCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketOrientedConnectedDistanceWeightedUnitCongestion
      S hfineCutoff hcoarseCoupling rate orientation first second
        observableFaceId hobservableFace)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId).attach

/-- The normalized connected joint mass is bounded by one explicit finite
sum whose summands are distance fugacity times heat-free unit congestion. -/
theorem finePacketOrientedNormalizedConnectedJointMass_le_distanceWeightedUnitCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≤
      finePacketOrientedConnectedDistanceWeightedUnitCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation first second
          observableFaceId hobservableFace := by
  unfold finePacketOrientedNormalizedConnectedJointMass
    finePacketOrientedConnectedDistanceWeightedUnitCongestionMass
  apply listQSum_mono_local
  intro entry _hentry
  cases orientation with
  | forward =>
      exact finePacketForwardNormalizedJointPairWeight_le_connectedWeight
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate hrate1
          first second observableFaceId hobservableFace entry.1 entry.2
  | reverse =>
      exact finePacketReverseNormalizedJointPairWeight_le_connectedWeight
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate hrate1
          first second observableFaceId hobservableFace entry.1 entry.2

/-! ## 4. Axiom audit -/

#print axioms finePacketOrientedNormalizedJointPairWeight
#print axioms finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_congestion
#print axioms finePacketOrientedNormalizedJointPairWeight_le_suppression_mul_unitCongestion
#print axioms finePacketOrientedJointUnitReferenceCongestion_nonnegative
#print axioms finePacketOrientedConnectedDistanceWeightedUnitCongestion
#print axioms finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
#print axioms finePacketOrientedNormalizedJointPairWeight_le_distanceWeightedUnitCongestion
#print axioms finePacketOrientedNormalizedConnectedJointMass
#print axioms finePacketOrientedConnectedDistanceWeightedUnitCongestionMass
#print axioms finePacketOrientedNormalizedConnectedJointMass_le_distanceWeightedUnitCongestionMass

end YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
