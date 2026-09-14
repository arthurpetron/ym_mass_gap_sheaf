/-
# A whole-forest code recovers both original ordered spatial lists

Replica tags distinguish the lists. Their order is canonical: both are
filters of the same literal physical plaquette list. Equal membership
therefore gives exact list equality, not just a permutation. This is the
missing spatial input to the existing whole-label reconstruction theorem.
-/

import YMGap.Continuum.BF4ExactSlabSpatialForestCode

namespace YMGap.Continuum.BF4ExactSlabSpatialForestRecovery

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
open YMGap.Continuum.BF4ExactSlabSpatialForestCode
open YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal
open YMGap.Continuum.BF4ExactSlabSpatialDefectReconstruction
open YMGap.Continuum.BF4ExactSlabOddFaceIncidence
open YMGap.Continuum.Z4SpatialDefectTemporalDecoder

theorem filter_eq_of_membership {A : Type} (xs : List A) (p q : A → Bool)
    (he : ∀ x, x ∈ xs.filter p ↔ x ∈ xs.filter q) : xs.filter p=xs.filter q := by
  apply List.filter_congr
  intro x hx
  have hf : p x=true → q x=true := fun hp => (List.mem_filter.mp ((he x).mp (List.mem_filter.mpr ⟨hx,hp⟩))).2
  have hb : q x=true → p x=true := fun hq => (List.mem_filter.mp ((he x).mpr (List.mem_filter.mpr ⟨hx,hq⟩))).2
  cases hp : p x <;> cases hq : q x <;> simp only [hp,hq,Bool.false_eq_true] at hf hb ⊢
  · exact False.elim (hb True.intro)
  · exact False.elim (hf True.intro)

theorem spatial_list_eq_of_membership (margin : Nat) (left right : EdgeLabelling)
    (he : ∀ face, face ∈ spatialOddFaces margin left ↔ face ∈ spatialOddFaces margin right) :
    spatialOddFaces margin left=spatialOddFaces margin right := by
  unfold spatialOddFaces spatialFaces oddFaces oddSelection at he ⊢
  simp only [List.filter_filter] at he ⊢
  exact filter_eq_of_membership _ _ _ he

theorem left_occurrence_mem (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (face : Z4Plaq) :
    (false,face) ∈ occurrences margin pair ↔ face ∈ spatialOddFaces margin pair.1 := by
  constructor
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨f,hf,he⟩ := List.mem_map.mp hm
      have hface : f=face := congrArg Prod.snd he
      exact hface ▸ hf
    · obtain ⟨f,_,he⟩ := List.mem_map.mp hm
      have ht := congrArg Prod.fst he
      contradiction
  · intro hm
    exact List.mem_append_left _ (List.mem_map.mpr ⟨face,hm,rfl⟩)

theorem right_occurrence_mem (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (face : Z4Plaq) :
    (true,face) ∈ occurrences margin pair ↔ face ∈ spatialOddFaces margin pair.2 := by
  constructor
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨f,_,he⟩ := List.mem_map.mp hm
      have ht := congrArg Prod.fst he
      contradiction
    · obtain ⟨f,hf,he⟩ := List.mem_map.mp hm
      have hface : f=face := congrArg Prod.snd he
      exact hface ▸ hf
  · intro hm
    exact List.mem_append_right _ (List.mem_map.mpr ⟨face,hm,rfl⟩)

theorem code_recover_spatial {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : Locality margin left) (hr : Locality margin right) (he : code margin left=code margin right) :
    spatialOddFaces margin left.1=spatialOddFaces margin right.1 ∧
      spatialOddFaces margin left.2=spatialOddFaces margin right.2 := by
  constructor
  · apply spatial_list_eq_of_membership
    intro face
    rw [← left_occurrence_mem margin left,← left_occurrence_mem margin right]
    exact code_eq_occurrences hl hr he (false,face)
  · apply spatial_list_eq_of_membership
    intro face
    rw [← right_occurrence_mem margin left,← right_occurrence_mem margin right]
    exact code_eq_occurrences hl hr he (true,face)

end YMGap.Continuum.BF4ExactSlabSpatialForestRecovery

#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRecovery.filter_eq_of_membership
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRecovery.spatial_list_eq_of_membership
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRecovery.left_occurrence_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRecovery.right_occurrence_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestRecovery.code_recover_spatial
