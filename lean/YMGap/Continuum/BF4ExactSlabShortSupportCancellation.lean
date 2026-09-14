/-
# Exact cancellation of original coefficients on fewer than twelve faces

Separating selections vanish by the existing original Haar factorization.
For connected selections, the original representation expansion and both
original replica filters leave no pair on a support of size below twelve.
The statement holds for every rational nome and every cutoff and margin.
This is a signed coefficient identity, not a positive response estimate.
-/

import YMGap.Continuum.BF4ExactSlabRetainedSelectedArea

namespace YMGap.Continuum.BF4ExactSlabShortSupportCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabRetainedSelectedArea
open YMGap.Continuum.BF4ExactSlabShiftedProbeCoveredExpansion
open YMGap.Continuum.BF4ExactSlabShiftedProbeLeafFilter
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabThermodynamicBaseCompatibility (enlarge)
open YMGap.Continuum.BF4ExactSlabThermodynamicProbeResponse (shiftedProbe)
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

theorem coefficient_leaf_filtered (w : Q') (K margin time : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hi : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges (responseExtent margin)) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈
      listQSum (weightedPairTerm w K margin)
        (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)) :=
  Q'.eqv_trans _ _ _ (coefficient_cut_filtered w K margin time ids hn hi) (weighted_leaf_filter w K margin _)

theorem short_retained_pairs_empty {K margin time : Nat} {ids : List Nat}
    (hi : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hshort : ids.length < 12) :
    (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)) = [] := by
  cases he : (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)) with
  | nil => rfl
  | cons pair rest =>
    have hm : pair ∈ (((labels K ids).filter (pairKeep margin time)).filter (pairLeafKeep margin)) := by
      rw [he]; exact List.mem_cons_self
    exact False.elim (Nat.not_le_of_gt hshort (original_retained_selected_minimum_twelve hi hm))

theorem connected_short_coefficient_zero (w : Q') (K margin : Nat) (ids : List Nat)
    (hi : ids ∈ connectedSelections (responseExtent margin) (edgesOf (sliceFace margin 0))
      (edgesOf (sliceFace margin 3)) (slabPhysicalFaceEdges (responseExtent margin)))
    (hshort : ids.length < 12) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈ 0 := by
  have hf := coefficient_leaf_filtered w K margin margin ids
    (selected_nodup (CayleyParentInj.range_nodup _) (List.mem_filter.mp hi).1)
    (fun id hm => selected_mem (List.mem_filter.mp hi).1 id hm)
  rw [short_retained_pairs_empty hi hshort] at hf
  exact hf

/-- No connectedness premise: every original selected coefficient below size twelve vanishes. -/
theorem original_short_coefficient_zero (w : Q') (K margin : Nat) (ids : List Nat)
    (hi : ids ∈ selections (slabPhysicalFaceEdges (responseExtent margin)))
    (hshort : ids.length < 12) :
    connectedCoefficient w K (responseExtent margin)
      (lower (enlarge margin shiftedProbe)) (upper (enlarge margin shiftedProbe)) ids ≈ 0 := by
  cases hk : keep (responseExtent margin) (edgesOf (sliceFace margin 0)) (edgesOf (sliceFace margin 3)) ids with
  | false =>
    exact coefficient_zero_of_discard w K (responseExtent margin) _ _ _ _
      (lower_supported _) (upper_supported _) (lower_link_local margin) (upper_link_local margin) ids hk
  | true => exact connected_short_coefficient_zero w K margin ids (List.mem_filter.mpr ⟨hi,hk⟩) hshort

end YMGap.Continuum.BF4ExactSlabShortSupportCancellation

#print axioms YMGap.Continuum.BF4ExactSlabShortSupportCancellation.coefficient_leaf_filtered
#print axioms YMGap.Continuum.BF4ExactSlabShortSupportCancellation.short_retained_pairs_empty
#print axioms YMGap.Continuum.BF4ExactSlabShortSupportCancellation.connected_short_coefficient_zero
#print axioms YMGap.Continuum.BF4ExactSlabShortSupportCancellation.original_short_coefficient_zero
