/-
# Global normalization of the connected cross-scale carrier

For a fixed positive fine-source pair, the oriented target weights form two
complete tilted rows.  Dividing their product by the exact row-product mass
and summing the full target-pair carrier therefore returns exactly the actual
fine source-pair weight.

Deleting zero fine sources preserves the fine partition, so summing over all
positive source pairs returns the exact square of the fine physical
partition.  This module packages the connected subcarrier and the refined
distance/residual/ground-normalized upper carrier globally and proves:

* the global normalized connected fraction is at most one; and
* it is bounded by the global refined carrier divided by the same partition
  square.

The latter quotient is the exact remaining component-entropy obligation.  No
strict or volume-uniform bound on it is asserted here.

Constructive contract: finite Cartesian sums, exact row normalization, and
positive rational division only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPartition

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

/-! ## 1. Exact normalization of one oriented target-pair row -/

def finePacketOrientedNormalizedFullJointMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) : Q' :=
  listQSum
    (finePacketOrientedNormalizedJointPairWeight
      S hfineCutoff hcoarseCoupling orientation first second)
    (cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings)

theorem finePacketOrientedFullEnvelopeSum_eqv_normalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    listQSum
        (finePacketOrientedLocalizedRawPairWeight
          S orientation first.1 second.1)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  cases orientation with
  | forward =>
      exact finePacketForwardFullEnvelopeSum_eqv_orientedNormalizationMass
        S hfineCutoff first second
  | reverse =>
      exact finePacketReverseFullEnvelopeSum_eqv_orientedNormalizationMass
        S hfineCutoff first second

/-- A complete normalized target-pair row has precisely its fine source-pair
mass; no target-state or volume factor remains. -/
theorem finePacketOrientedNormalizedFullJointMass_eqv_sourcePairWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedNormalizedFullJointMass
        S hfineCutoff hcoarseCoupling orientation first second ≈
      finePacketFineSourceRawPairWeight S first.1 second.1 := by
  let sourceWeight := finePacketFineSourceRawPairWeight
    S first.1 second.1
  let targetWeight := finePacketOrientedLocalizedRawPairWeight
    S orientation first.1 second.1
  let states := cartesian S.coarse.physicalLabellings
    S.coarse.physicalLabellings
  let row := finePacketOrientedEnvelopeNormalizationMass S first second
  let reciprocal := Q'.recipPos row
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)
  have htarget : listQSum targetWeight states ≈ row :=
    finePacketOrientedFullEnvelopeSum_eqv_normalizationMass
      S hfineCutoff orientation first second
  have hinner :
      listQSum (fun pair => targetWeight pair * reciprocal) states ≈
        (1 : Q') := by
    refine Q'.eqv_trans _ (listQSum targetWeight states * reciprocal) _
      (listQSum_mul_right targetWeight reciprocal states) ?_
    refine Q'.eqv_trans _ (row * reciprocal) _
      (Q'.mul_eqv_congr_right _ _ _ htarget) ?_
    exact Q'.mul_recipPos_eqv row
      (finePacketOrientedEnvelopeNormalizationMass_pos
        S hfineCutoff hcoarseCoupling first second)
  unfold finePacketOrientedNormalizedFullJointMass
    finePacketOrientedNormalizedJointPairWeight
    finePacketOrientedJointGibbsRawPairWeight Q'.divPos
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => sourceWeight * (targetWeight pair * reciprocal))
      states) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact Q'.mul_assoc_eqv sourceWeight (targetWeight pair) reciprocal
  refine Q'.eqv_trans _
    (sourceWeight *
      listQSum (fun pair => targetWeight pair * reciprocal) states) _
    (listQSum_mul_left sourceWeight
      (fun pair => targetWeight pair * reciprocal) states) ?_
  refine Q'.eqv_trans _ (sourceWeight * 1) _
    (Q'.mul_eqv_congr_left sourceWeight _ _ hinner) ?_
  exact Q'.mul_one_eqv sourceWeight

private theorem finePacketOrientedNormalizedJointPairWeight_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketOrientedNormalizedJointPairWeight
      S hfineCutoff hcoarseCoupling orientation first second pair := by
  unfold finePacketOrientedNormalizedJointPairWeight Q'.divPos
    finePacketOrientedJointGibbsRawPairWeight
    finePacketFineSourceRawPairWeight
  have htarget : (0 : Q') ≤ finePacketOrientedLocalizedRawPairWeight
      S orientation first.1 second.1 pair := by
    cases orientation with
    | forward =>
        exact finePacketForwardLocalizedRawPairWeight_nonnegative
          S first.1 second.1 pair
    | reverse =>
        exact finePacketReverseLocalizedRawPairWeight_nonnegative
          S first.1 second.1 pair
  exact Q'.mul_nonneg _ _
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt first.2.2)
        (Q'.le_of_lt second.2.2))
      htarget)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (finePacketOrientedEnvelopeNormalizationMass_pos
          S hfineCutoff hcoarseCoupling first second)))

/-- Restricting a normalized target row to the connected active subcarrier
cannot exceed its exact source-pair mass. -/
theorem finePacketOrientedNormalizedConnectedJointMass_le_sourcePairWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≤
      finePacketFineSourceRawPairWeight S first.1 second.1 := by
  let weight := finePacketOrientedNormalizedJointPairWeight
    S hfineCutoff hcoarseCoupling orientation first second
  have hsub :
      listQSum weight
          (finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 observableFaceId) ≤
        listQSum weight
          (cartesian S.coarse.physicalLabellings
            S.coarse.physicalLabellings) := by
    apply listQSum_le_of_injective_nodup
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId)
      (cartesian S.coarse.physicalLabellings
        S.coarse.physicalLabellings)
      weight weight (fun pair => pair)
    · exact finePacketFaceResponseConnectedActivePairs_nodup
        S first.1 second.1 observableFaceId
    · exact cartesian_nodup
        S.coarse.physicalLabellings S.coarse.physicalLabellings
        (slabPhysicalLabellings_nodup S.coarse)
        (slabPhysicalLabellings_nodup S.coarse)
    · intro pair hpair
      exact (List.mem_filter.mp (List.mem_filter.mp hpair).1).1
    · intro left _ right _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact finePacketOrientedNormalizedJointPairWeight_nonnegative
        S hfineCutoff hcoarseCoupling orientation first second pair
  exact Q'.le_trans' _ _ _
    (by
      unfold finePacketOrientedNormalizedConnectedJointMass
      simpa only [listQSum_attach] using hsub)
    (Q'.le_of_eqv
      (finePacketOrientedNormalizedFullJointMass_eqv_sourcePairWeight
        S hfineCutoff hcoarseCoupling orientation first second))

/-! ## 2. Positive fine sources sum to the genuine partition -/

private theorem finePhysicalTermSum_eqv_positiveAux
    (S : SlabScalePair) :
    ∀ (sources : List EdgeLabelling)
      (hphysical : ∀ source, source ∈ sources →
        source ∈ S.fine.physicalLabellings),
      listQSum S.fine.physicalTerm sources ≈
        listQSum
          (fun source : PositivePhysicalSource S =>
            S.fine.physicalTerm source.1)
          (positivePhysicalSourcesAux S sources hphysical)
  | [], _ => Q'.eqv_refl 0
  | source :: tail, hphysical => by
      let htail : ∀ item, item ∈ tail →
          item ∈ S.fine.physicalLabellings :=
        fun item hitem =>
          hphysical item (List.mem_cons_of_mem source hitem)
      by_cases hpositive : (0 : Q') < S.fine.physicalTerm source
      · simp only [listQSum, positivePhysicalSourcesAux, dif_pos hpositive]
        exact Q'.add_eqv_congr'
          (Q'.eqv_refl _)
          (finePhysicalTermSum_eqv_positiveAux S tail htail)
      · simp only [listQSum, positivePhysicalSourcesAux, dif_neg hpositive]
        refine Q'.eqv_trans _
          (0 + listQSum S.fine.physicalTerm tail) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (physicalTerm_eqv_zero_of_not_positive
              S.fine source hpositive)
            (Q'.eqv_refl _)
        · exact Q'.eqv_trans _ _ _
            (Q'.eqv_of_eq (Q'.zero_add' _))
            (finePhysicalTermSum_eqv_positiveAux S tail htail)

theorem finePositivePhysicalSources_weight_total
    (S : SlabScalePair) :
    listQSum
        (fun source : PositivePhysicalSource S =>
          S.fine.physicalTerm source.1)
        (positivePhysicalSources S) ≈
      S.fine.physicalPartition := by
  have hpositive := finePhysicalTermSum_eqv_positiveAux
    S S.fine.physicalLabellings (fun _ hsource => hsource)
  apply Q'.eqv_trans _ _ _ (Q'.eqv_symm hpositive)
  exact Q'.eqv_refl _

theorem finePositivePhysicalSourcePairs_weight_total
    (S : SlabScalePair) :
    listQSum
        (fun pair : PositivePhysicalSourcePair S =>
          finePacketFineSourceRawPairWeight S pair.1.1 pair.2.1)
        (positivePhysicalSourcePairs S) ≈
      S.fine.physicalPartition * S.fine.physicalPartition := by
  let sourceWeight := fun source : PositivePhysicalSource S =>
    S.fine.physicalTerm source.1
  have hcart := listQSum_cartesian_product
    sourceWeight sourceWeight
    (positivePhysicalSources S) (positivePhysicalSources S)
  unfold positivePhysicalSourcePairs
  refine Q'.eqv_trans _
    (listQSum sourceWeight (positivePhysicalSources S) *
      listQSum sourceWeight (positivePhysicalSources S)) _ ?_ ?_
  · simpa only [sourceWeight, finePacketFineSourceRawPairWeight] using hcart
  refine Q'.eqv_trans _
    (S.fine.physicalPartition *
      listQSum sourceWeight (positivePhysicalSources S)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePositivePhysicalSources_weight_total S)
  · exact Q'.mul_eqv_congr_left _ _ _
      (finePositivePhysicalSources_weight_total S)

/-! ## 3. Global connected and refined carrier fractions -/

def finePacketGlobalNormalizedConnectedJointMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation pair.1 pair.2
          observableFaceId)
    (positivePhysicalSourcePairs S)

def finePacketGlobalDistanceResidualGroundCongestionMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketOrientedConnectedDistanceResidualGroundCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation pair.1 pair.2
          observableFaceId hobservableFace)
    (positivePhysicalSourcePairs S)

def finePacketGlobalNormalizedConnectedJointFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketGlobalNormalizedConnectedJointMass
      S hfineCutoff hcoarseCoupling orientation observableFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

theorem finePacketGlobalNormalizedConnectedJointMass_le_partitionSquare
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      S.fine.physicalPartition * S.fine.physicalPartition := by
  unfold finePacketGlobalNormalizedConnectedJointMass
  exact Q'.le_trans' _ _ _
    (listQSum_mono_local _ _ (positivePhysicalSourcePairs S)
      (fun pair _ =>
        finePacketOrientedNormalizedConnectedJointMass_le_sourcePairWeight
          S hfineCutoff hcoarseCoupling orientation pair.1 pair.2
            observableFaceId))
    (Q'.le_of_eqv (finePositivePhysicalSourcePairs_weight_total S))

theorem finePacketGlobalNormalizedConnectedJointFraction_le_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      (1 : Q') := by
  unfold finePacketGlobalNormalizedConnectedJointFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNormalizedConnectedJointMass_le_partitionSquare
      S hfineCutoff hcoarseCoupling orientation observableFaceId)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (S.fine.physicalPartition * S.fine.physicalPartition)))

theorem finePacketGlobalNormalizedConnectedJointMass_le_refinedCarrier
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketGlobalDistanceResidualGroundCongestionMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNormalizedConnectedJointMass
    finePacketGlobalDistanceResidualGroundCongestionMass
  apply listQSum_mono_local
  intro pair _hpair
  exact
    finePacketOrientedNormalizedConnectedJointMass_le_distanceResidualGroundCongestionMass
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate
        orientation pair.1 pair.2 observableFaceId hobservableFace

/-! ## 4. Axiom audit -/

#print axioms finePacketOrientedNormalizedFullJointMass
#print axioms finePacketOrientedFullEnvelopeSum_eqv_normalizationMass
#print axioms finePacketOrientedNormalizedFullJointMass_eqv_sourcePairWeight
#print axioms finePacketOrientedNormalizedConnectedJointMass_le_sourcePairWeight
#print axioms finePositivePhysicalSources_weight_total
#print axioms finePositivePhysicalSourcePairs_weight_total
#print axioms finePacketGlobalNormalizedConnectedJointMass
#print axioms finePacketGlobalDistanceResidualGroundCongestionMass
#print axioms finePacketGlobalNormalizedConnectedJointFraction
#print axioms finePacketGlobalNormalizedConnectedJointMass_le_partitionSquare
#print axioms finePacketGlobalNormalizedConnectedJointFraction_le_one
#print axioms finePacketGlobalNormalizedConnectedJointMass_le_refinedCarrier

end YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
