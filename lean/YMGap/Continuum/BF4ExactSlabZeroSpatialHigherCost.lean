/-
# Every surviving original non-tube term pays a defect cost

In the zero-spatial sector, vanishing higher-label count forces every
nonzero original connected pair to be the literal canonical tube pair.
Therefore each original non-tube coefficient can be filtered exactly to
pairs with a spatial odd-face defect or a positive higher-label count.
The original weights, multiplicities and signed Haar terms are unchanged.
This removes a zero-cost sector; it does not yet count the remaining
spatial patterns or bound their aggregate signed contribution.
-/

import YMGap.Continuum.BF4ExactSlabZeroSpatialChannels
import YMGap.Continuum.BF4ExactSlabParityHigherPairBound
import YMGap.Continuum.BF4ExactSlabShortSupportCancellation

namespace YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RGTransport
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteParityHigherProduct
open YMGap.Continuum.SU2ParityHigherHeatEnvelope
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabZeroSpatialChannels
open YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
open YMGap.Continuum.BF4ExactSlabParityHigherPairBound
open YMGap.Continuum.BF4ExactSlabShortSupportCancellation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem higherCount_zero_small (state : Nat → Nat) : ∀ ids : List Nat,
    higherCount state ids = 0 → ∀ id, id ∈ ids → state id ≤ 1
  | [], _, _, hi => by cases hi
  | head::ids, hz, id, hi => by
    change state head/2 + higherCount state ids = 0 at hz
    rcases List.mem_cons.mp hi with he | ht
    · subst id
      omega
    · exact higherCount_zero_small state ids (by omega) id ht

theorem noHigher_nonzero_pair_pin {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = [])
    (hz : pairHigher margin pair = 0) (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) :
    pair = tubePair margin := by
  have hc := nonzero_pair_checks margin pair.1 pair.2 hl hne
  have hb (id : Nat) (hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
      pair.1 id ≤ 1 ∧ pair.2 id ≤ 1 := by
    unfold pairHigher at hz
    exact ⟨higherCount_zero_small pair.1 _ (by omega) id hi,
      higherCount_zero_small pair.2 _ (by omega) id hi⟩
  have hout (id : Nat) (hi : id ∉ slabPhysicalFaceEdges (responseExtent margin)) :=
    outside K ids pair hp id (fun hid => hi (selected_mem hs id hid))
  apply Prod.ext
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · have he := mixed_parity_pin margin pair.1 hl hc.1 id hi
      have h := (hb id hi).1
      change pair.1 id = tubeLabelling margin id
      omega
    · simpa only [tubePair, tubeLabelling, hi, false_and, ↓reduceIte] using (hout id hi).1
  · funext id
    by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
    · have he := partition_parity_zero margin pair.2 hr hc.2 id hi
      have h := (hb id hi).2
      change pair.2 id = 0
      omega
    · exact (hout id hi).2

theorem nonTube_noHigher_zero {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids) (ht : ids ≠ tubeIds margin)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = [])
    (hz : pairHigher margin pair = 0) : pairTerm margin pair.1 pair.2 ≈ 0 := by
  by_cases he : pairTerm margin pair.1 pair.2 ≈ 0
  · exact he
  · have hpin := noHigher_nonzero_pair_pin hs hp hl hr hz he
    have htp := tubePair_enumerated K margin hK
    rw [← hpin] at htp
    exact False.elim (ht (selected_support_eq (CayleyParentInj.range_nodup _)
      hs (tubeIds_selected margin) hp htp))

theorem nonTube_nonzero_higher {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids) (ht : ids ≠ tubeIds margin)
    (hl : spatialOddFaces margin pair.1 = []) (hr : spatialOddFaces margin pair.2 = [])
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) : 0 < pairHigher margin pair := by
  by_cases hz : pairHigher margin pair = 0
  · exact False.elim (hne (nonTube_noHigher_zero hK hs hp ht hl hr hz))
  · omega

/-- Keep spatial odd-face defects or higher-label quotient units; these are different costs. -/
def defectKeep (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  !decide (spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = []) ||
    decide (0 < pairHigher margin pair)

theorem rejected_weight_zero (w : Q') {K margin : Nat} {ids : List Nat}
    {pair : EdgeLabelling × EdgeLabelling} (hK : 1 ≤ K)
    (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hp : pair ∈ labels K ids) (ht : ids ≠ tubeIds margin)
    (hk : defectKeep margin pair = false) : weightedPairTerm w K margin pair ≈ 0 := by
  by_cases hsp : spatialOddFaces margin pair.1 = [] ∧ spatialOddFaces margin pair.2 = []
  · by_cases hh : 0 < pairHigher margin pair
    · simp only [defectKeep, hsp, hh, decide_true] at hk
      cases hk
    · have hz := nonTube_noHigher_zero hK hs hp ht hsp.1 hsp.2 (by omega)
      exact Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hz) (Q'.mul_zero_eqv _)
  · simp only [defectKeep, hsp, decide_false, Bool.not_false, Bool.true_or] at hk
    cases hk

/-- Exact deletion on the SAME retained pairs, without requiring their moment checks as hypotheses. -/
theorem original_nonTube_defect_filter (w : Q') (K margin time : Nat) (ids : List Nat)
    (hK : 1 ≤ K) (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (ht : ids ≠ tubeIds margin) :
    listQSum (weightedPairTerm w K margin)
      (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)) ≈
    listQSum (weightedPairTerm w K margin)
      ((((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)).filter (defectKeep margin)) :=
  FiniteSelectionMobius.sum_filter_zero _ _ _ (fun _ hp hk =>
    rejected_weight_zero w hK hs (List.mem_filter.mp (List.mem_filter.mp hp).1).1 ht hk)

/-- The actual original coefficient now sums only pairs paying at least one kind of defect cost. -/
theorem original_nonTube_coefficient (w : Q') (K margin time : Nat) (ids : List Nat)
    (hK : 1 ≤ K) (hs : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (ht : ids ≠ tubeIds margin) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈
    listQSum (weightedPairTerm w K margin)
      ((((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)).filter (defectKeep margin)) :=
  Q'.eqv_trans _ _ _ (coefficient_leaf_filtered w K margin time ids
    (selected_nodup (CayleyParentInj.range_nodup _) hs) (fun id hi => selected_mem hs id hi))
    (original_nonTube_defect_filter w K margin time ids hK hs ht)

end YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost

#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.higherCount_zero_small
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.noHigher_nonzero_pair_pin
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.nonTube_noHigher_zero
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.nonTube_nonzero_higher
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.defectKeep
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.rejected_weight_zero
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.original_nonTube_defect_filter
#print axioms YMGap.Continuum.BF4ExactSlabZeroSpatialHigherCost.original_nonTube_coefficient
