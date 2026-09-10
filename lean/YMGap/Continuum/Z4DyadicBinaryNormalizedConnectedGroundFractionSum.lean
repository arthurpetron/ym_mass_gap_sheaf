/-
# Restore the literal ground-row normalization fraction

The parity-ground summand used to expose unit congestion is not merely below
the full tilted-row product: its quotient by that product is an explicit
probability fraction.  Dropping this fraction loses the normalization needed
to absorb exterior backgrounds.

This module restores it.  For every lowering pair, the normalized joint
weight factors exactly as

`suppression * unitCongestion * groundRowFraction`,

where `0 <= groundRowFraction <= 1`.  Combining that identity with residual
heat extraction and summing the attached connected carrier yields the refined
interface

`normalized connected mass`
`  <= sum_connected distancePower * residualHeat`
`       * unitCongestion * groundRowFraction`.

No estimate of the remaining normalized carrier is asserted.

Constructive contract: positive rational division, exact finite sums, and
checked lowering/path witnesses only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedResidualHeatSum

namespace YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum

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
open YMGap.Continuum.Z4DyadicBinaryJointResidualHeatSuppression
open YMGap.Continuum.Z4DyadicBinaryJointUnitReferenceCongestion
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedResidualHeatSum
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

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_num_eqv_local {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (h : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _ h

private theorem divPos_mul_left_eqv_local
    (left numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (left * numerator) denominator hdenominator ≈
      left * Q'.divPos numerator denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_assoc_eqv left numerator (Q'.recipPos denominator hdenominator)

/-- Quotient through a positive intermediate denominator.  Keeping this
algebra generic prevents the large dependent slab expressions from being
unfolded during cancellation. -/
private theorem divPos_through_positive_local
    (numerator middle denominator : Q')
    (hmiddle : (0 : Q') < middle)
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos numerator denominator hdenominator ≈
      Q'.divPos numerator middle hmiddle *
        Q'.divPos middle denominator hdenominator := by
  apply divPos_eqv_of_eqv_mul_local hdenominator
  apply Q'.eqv_symm
  refine Q'.eqv_trans _
    (Q'.divPos numerator middle hmiddle *
      (Q'.divPos middle denominator hdenominator * denominator)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (Q'.divPos numerator middle hmiddle * middle) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.divPos_mul_eqv middle denominator hdenominator)
  · exact Q'.divPos_mul_eqv numerator middle hmiddle

/-! ## 1. The ground summand as a row probability fraction -/

/-- The literal parity-ground pair mass divided by the exact product of the
two complete tilted-row masses. -/
def finePacketOrientedParityGroundRowFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) : Q' :=
  Q'.divPos
    (finePacketOrientedParityGroundReferenceNormalizationMass
      S orientation first.1 second.1)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

theorem finePacketOrientedParityGroundRowFraction_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    (0 : Q') ≤ finePacketOrientedParityGroundRowFraction
      S hfineCutoff hcoarseCoupling orientation first second := by
  unfold finePacketOrientedParityGroundRowFraction Q'.divPos
  exact Q'.mul_nonneg _ _
    (Q'.le_of_lt
      (finePacketOrientedParityGroundReferenceNormalizationMass_pos
        S hfineCutoff hcoarseCoupling orientation first second))
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (finePacketOrientedEnvelopeNormalizationMass_pos
          S hfineCutoff hcoarseCoupling first second)))

theorem finePacketOrientedParityGroundRowFraction_le_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedParityGroundRowFraction
        S hfineCutoff hcoarseCoupling orientation first second ≤
      (1 : Q') := by
  unfold finePacketOrientedParityGroundRowFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (finePacketOrientedParityGroundReferenceNormalizationMass_le_rowNormalization
      S hfineCutoff hcoarseCoupling orientation first second)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (finePacketOrientedEnvelopeNormalizationMass S first second)))

/-! ## 2. Exact restoration of the dropped normalization factor -/

/-- The parity-ground reference for one target pair divided by the complete
two-row normalization.  Naming this quotient keeps the exact factorization
interface small enough for deterministic elaboration. -/
def finePacketOrientedNormalizedParityGroundReferenceWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  Q'.divPos
    (finePacketOrientedJointParityGroundReferenceWeight
      S orientation first.1 second.1 pair)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

/-- Unit congestion with the literal ground-row probability fraction
restored. -/
def finePacketOrientedGroundNormalizedUnitCongestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketOrientedJointUnitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair *
    finePacketOrientedParityGroundRowFraction
      S hfineCutoff hcoarseCoupling orientation first second

theorem finePacketOrientedGroundNormalizedUnitCongestion_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedGroundNormalizedUnitCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair := by
  unfold finePacketOrientedGroundNormalizedUnitCongestion
  exact Q'.mul_nonneg _ _
    (finePacketOrientedJointUnitReferenceCongestion_nonnegative
      S hfineCutoff hcoarseCoupling orientation first second pair)
    (finePacketOrientedParityGroundRowFraction_nonnegative
      S hfineCutoff hcoarseCoupling orientation first second)

/-- Unit congestion times the ground-row fraction is exactly the complete
parity-ground reference divided by the full row-product normalization. -/
theorem finePacketOrientedReferenceDivRow_eqv_unitCongestion_mul_groundFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketOrientedNormalizedParityGroundReferenceWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≈
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation first second pair := by
  have hground : (0 : Q') <
      finePacketOrientedParityGroundReferenceNormalizationMass
        S orientation first.1 second.1 :=
    finePacketOrientedParityGroundReferenceNormalizationMass_pos
      S hfineCutoff hcoarseCoupling orientation first second
  have hrow : (0 : Q') <
      finePacketOrientedEnvelopeNormalizationMass S first second :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second
  have hfactor := divPos_through_positive_local
    (finePacketOrientedJointParityGroundReferenceWeight
      S orientation first.1 second.1 pair)
    (finePacketOrientedParityGroundReferenceNormalizationMass
      S orientation first.1 second.1)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    hground hrow
  have hfactor' :
      finePacketOrientedNormalizedParityGroundReferenceWeight
          S hfineCutoff hcoarseCoupling orientation first second pair ≈
        finePacketOrientedJointReferenceCongestionRatio
            S hfineCutoff hcoarseCoupling orientation first second pair *
          finePacketOrientedParityGroundRowFraction
            S hfineCutoff hcoarseCoupling orientation first second := by
    simpa only [finePacketOrientedNormalizedParityGroundReferenceWeight,
      finePacketOrientedJointReferenceCongestionRatio,
      finePacketOrientedParityGroundRowFraction] using hfactor
  have hcongestion :=
    finePacketOrientedJointReferenceCongestionRatio_eqv_unitReferenceCongestion
      S hfineCutoff hcoarseCoupling orientation first second pair
  refine Q'.eqv_trans _ _ _ hfactor' ?_
  unfold finePacketOrientedGroundNormalizedUnitCongestion
  exact Q'.mul_eqv_congr_right _ _ _ hcongestion

/-- Exact normalized factorization.  The earlier pointwise inequality is this
identity followed by the harmless bound `groundRowFraction <= 1`. -/
theorem finePacketOrientedNormalizedJointPairWeight_eqv_suppression_mul_unitCongestion_mul_groundFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≈
      finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedGroundNormalizedUnitCongestion
          S hfineCutoff hcoarseCoupling orientation first second pair := by
  let row := finePacketOrientedEnvelopeNormalizationMass S first second
  have hrow : (0 : Q') < row :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second
  have hraw :=
    finePacketOrientedJointGibbsRawPairWeight_eqv_suppression_mul_reference
      S hfineCutoff orientation first second pair hlowering
  unfold finePacketOrientedNormalizedJointPairWeight
  refine Q'.eqv_trans _
    (Q'.divPos
      (finePacketOrientedJointSuppressionFactor
          S orientation first.1 second.1 pair *
        finePacketOrientedJointParityGroundReferenceWeight
          S orientation first.1 second.1 pair)
      row hrow) _
    (divPos_num_eqv_local hrow hraw) ?_
  refine Q'.eqv_trans _
    (finePacketOrientedJointSuppressionFactor
        S orientation first.1 second.1 pair *
      Q'.divPos
        (finePacketOrientedJointParityGroundReferenceWeight
          S orientation first.1 second.1 pair)
        row hrow) _
    (divPos_mul_left_eqv_local _ _ row hrow) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (finePacketOrientedReferenceDivRow_eqv_unitCongestion_mul_groundFraction
      S hfineCutoff hcoarseCoupling orientation first second pair)

/-! ## 3. Distance, residual heat, and row fraction together -/

/-- The fully normalized connected summand keeps both the residual heat and
the literal ground-row probability fraction. -/
def finePacketOrientedConnectedDistanceResidualGroundCongestion
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
    (qpow rate
        (finePacketOrientedConnectedResidualHeatExponent
          S orientation first.1 second.1 observableFaceId entry.1 path) *
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation first second entry.1)

theorem finePacketOrientedNormalizedJointPairWeight_le_distanceResidualGroundCongestion
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
          finePacketOrientedGroundNormalizedUnitCongestion
            S hfineCutoff hcoarseCoupling orientation first second pair) := by
  have hexact :=
    finePacketOrientedNormalizedJointPairWeight_eqv_suppression_mul_unitCongestion_mul_groundFraction
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  have hsuppression :=
    finePacketOrientedConnectedPath_jointSuppression_le_distance_mul_residual
      S hfineCutoff rate hfineRate hcoarseRate orientation first second
        observableFaceId hobservableFace pair hlowering path
  have htail0 : (0 : Q') ≤
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation first second pair :=
    finePacketOrientedGroundNormalizedUnitCongestion_nonnegative
      S hfineCutoff hcoarseCoupling orientation first second pair
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hexact)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hsuppression htail0) ?_)
  exact Q'.le_of_eqv (Q'.mul_assoc_eqv _ _ _)

private theorem finePacketOrientedNormalizedJointPairWeight_le_connectedGroundWeight
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
      finePacketOrientedConnectedDistanceResidualGroundCongestion
        S hfineCutoff hcoarseCoupling rate orientation first second
          observableFaceId hobservableFace ⟨pair, hpair⟩ := by
  by_cases hzero : finePacketOrientedLocalizedRawPairWeight
      S orientation first.1 second.1 pair ≈ 0
  · have hnormalized :=
      finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
        S hfineCutoff hcoarseCoupling orientation first second pair hzero
    have hrate0 : (0 : Q') ≤ rate := Q'.le_trans' _ _ _
      S.fine.coupling_nonnegative hfineRate
    unfold finePacketOrientedConnectedDistanceResidualGroundCongestion
    dsimp only
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hnormalized)
      (Q'.mul_nonneg _ _
        (qpow_nonneg _ (qpow_nonneg rate hrate0 3) _)
        (Q'.mul_nonneg _ _
          (qpow_nonneg rate hrate0 _)
          (finePacketOrientedGroundNormalizedUnitCongestion_nonnegative
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
      finePacketOrientedNormalizedJointPairWeight_le_distanceResidualGroundCongestion
        S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
          orientation first second observableFaceId hobservableFace pair
          hlowering
          (finePacketFaceResponseConnectedActivePairPath
            S first.1 second.1 observableFaceId hobservableFace pair hpair)
    unfold finePacketOrientedConnectedDistanceResidualGroundCongestion
    simpa only using hbound

/-! ## 4. Sum the normalized connected carrier -/

def finePacketOrientedConnectedDistanceResidualGroundCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketOrientedConnectedDistanceResidualGroundCongestion
      S hfineCutoff hcoarseCoupling rate orientation first second
        observableFaceId hobservableFace)
    (finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId).attach

/-- Final normalized interface before component/terminal regrouping. -/
theorem finePacketOrientedNormalizedConnectedJointMass_le_distanceResidualGroundCongestionMass
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
      finePacketOrientedConnectedDistanceResidualGroundCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation first second
          observableFaceId hobservableFace := by
  unfold finePacketOrientedNormalizedConnectedJointMass
    finePacketOrientedConnectedDistanceResidualGroundCongestionMass
  apply listQSum_mono_local
  intro entry _hentry
  exact
    finePacketOrientedNormalizedJointPairWeight_le_connectedGroundWeight
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
        orientation first second observableFaceId hobservableFace
        entry.1 entry.2

/-! ## 5. Axiom audit -/

#print axioms finePacketOrientedParityGroundRowFraction
#print axioms finePacketOrientedParityGroundRowFraction_nonnegative
#print axioms finePacketOrientedParityGroundRowFraction_le_one
#print axioms finePacketOrientedNormalizedParityGroundReferenceWeight
#print axioms finePacketOrientedGroundNormalizedUnitCongestion
#print axioms finePacketOrientedGroundNormalizedUnitCongestion_nonnegative
#print axioms finePacketOrientedReferenceDivRow_eqv_unitCongestion_mul_groundFraction
#print axioms finePacketOrientedNormalizedJointPairWeight_eqv_suppression_mul_unitCongestion_mul_groundFraction
#print axioms finePacketOrientedConnectedDistanceResidualGroundCongestion
#print axioms finePacketOrientedNormalizedJointPairWeight_le_distanceResidualGroundCongestion
#print axioms finePacketOrientedConnectedDistanceResidualGroundCongestionMass
#print axioms finePacketOrientedNormalizedConnectedJointMass_le_distanceResidualGroundCongestionMass

end YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
