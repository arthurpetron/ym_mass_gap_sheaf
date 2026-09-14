/-
# The explicit tube pair belongs to the original representation enumeration

The support is the original ordered physical-index filter, not a new face
ordering. Its left labelling is the existing tubeLabelling and its right
labelling is zero. At every cutoff at least one, this exact pair appears
in the original labels list. Connectedness and moment filters are separate.
-/

import YMGap.Continuum.BF4ExactSlabLeadingCountUniqueness
import YMGap.Continuum.PairedPositiveFaceLabellingCompleteness

namespace YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.PairedPositiveFaceLabellingCompleteness
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabTubeSupportGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ThreeCutSaturation

theorem face_lookup {extent : Nat} {face : Z4Plaq}
    (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    slabPlaquetteAt extent ((boundaryCompleteSlabPlaquettes extent).idxOf face) = face := by
  have hb := List.idxOf_lt_length_of_mem hf
  exact (List.getElem_eq_getD (h := hb) fallbackPlaquette).symm.trans
    (LawfulBEq.eq_of_beq (List.findIdx_getElem (w := hb)))

theorem tube_small (margin id : Nat) : tubeLabelling margin id ≤ 1 := by
  unfold tubeLabelling
  split <;> decide

theorem tube_face_label (margin : Nat) (face : Z4Plaq)
    (hf : face ∈ boundaryCompleteSlabPlaquettes (responseExtent margin)) :
    tubeLabelling margin ((boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face) =
      if face ∈ tubeSides margin then 1 else 0 := by
  have hi : (boundaryCompleteSlabPlaquettes (responseExtent margin)).idxOf face ∈
      slabPhysicalFaceEdges (responseExtent margin) := List.mem_range.mpr (List.idxOf_lt_length_of_mem hf)
  simp only [tubeLabelling,hi,true_and,face_lookup hf]

theorem tube_positive_mem (margin : Nat) (face : Z4Plaq) :
    face ∈ positiveFaces (responseExtent margin) (tubeLabelling margin) ↔ face ∈ tubeSides margin := by
  constructor
  · intro h
    have hf := (List.mem_filter.mp h).1
    have hp := of_decide_eq_true (List.mem_filter.mp h).2
    rw [tube_face_label margin face hf] at hp
    by_cases ht : face ∈ tubeSides margin
    · exact ht
    · rw [if_neg ht] at hp
      exact False.elim (Nat.lt_irrefl 0 hp)
  · intro hf
    have hp := tubeSides_physical margin face hf
    exact List.mem_filter.mpr ⟨hp,decide_eq_true (by rw [tube_face_label margin face hp,if_pos hf]; decide)⟩

theorem tube_positive_perm (margin : Nat) :
    (positiveFaces (responseExtent margin) (tubeLabelling margin)).Perm (tubeSides margin) :=
  Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    (positiveFaces_nodup _ _) (tubeSides_nodup margin) (tube_positive_mem margin)

theorem tube_positive_window (margin : Nat) (face : Z4Plaq)
    (hf : face ∈ positiveFaces (responseExtent margin) (tubeLabelling margin)) : window margin face = true :=
  tube_window margin face ((tube_positive_mem margin face).mp hf)

def tubeIds (margin : Nat) : List Nat :=
  (slabPhysicalFaceEdges (responseExtent margin)).filter (fun id => decide (0 < tubeLabelling margin id))

theorem tubeIds_mem_iff (margin id : Nat) : id ∈ tubeIds margin ↔
    id ∈ slabPhysicalFaceEdges (responseExtent margin) ∧
      slabPlaquetteAt (responseExtent margin) id ∈ tubeSides margin := by
  by_cases hi : id ∈ slabPhysicalFaceEdges (responseExtent margin)
  all_goals by_cases hf : slabPlaquetteAt (responseExtent margin) id ∈ tubeSides margin
  all_goals simp [tubeIds,tubeLabelling,hi,hf]

theorem tubeIds_selected (margin : Nat) :
    tubeIds margin ∈ selections (slabPhysicalFaceEdges (responseExtent margin)) := filter_selected _ _

theorem tubeIds_nodup (margin : Nat) : (tubeIds margin).Nodup :=
  (CayleyParentInj.range_nodup _).filter _

theorem tube_outside (margin id : Nat) (hi : id ∉ tubeIds margin) : tubeLabelling margin id = 0 := by
  have hn := fun h => hi ((tubeIds_mem_iff margin id).mpr h)
  exact if_neg hn

def tubePair (margin : Nat) : EdgeLabelling × EdgeLabelling := (tubeLabelling margin,zeroEdgeLabelling)

theorem tubePair_enumerated (K margin : Nat) (hK : 1 ≤ K) : tubePair margin ∈ labels K (tubeIds margin) :=
  labels_complete K (tubeIds margin) (tubePair margin) (tubeIds_nodup margin)
    (fun id _ => ⟨Nat.le_trans (tube_small margin id) hK,Nat.zero_le _⟩)
    (fun _ hi => Or.inl (of_decide_eq_true (List.mem_filter.mp hi).2))
    (fun id hi => ⟨tube_outside margin id hi,rfl⟩)

end YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport

#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.face_lookup
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_small
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_face_label
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_positive_mem
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_positive_perm
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_positive_window
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubeIds
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubeIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubeIds_selected
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubeIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tube_outside
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubePair
#print axioms YMGap.Continuum.BF4ExactSlabCanonicalTubeSupport.tubePair_enumerated
