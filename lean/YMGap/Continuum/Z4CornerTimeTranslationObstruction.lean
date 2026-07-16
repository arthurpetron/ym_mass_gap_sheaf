/-
# The corner-box obstruction to a time-translation group

The current physical geometry has vertex coordinates in `Nat^4` and exhausts
the corner boxes `[0,n)^4`.  Positive Euclidean-time translation therefore has
no preimage for the time-zero boundary.  This module records the obstruction
in the kernel: every positive shift is non-surjective, has no right inverse,
and cannot permute a complete corner-box vertex list onto the enlarged box.

These facts do not obstruct the nonnegative translation semigroup on local
cylinder presentations.  They do rule out deriving full OS translation
invariance by pretending that this semigroup is a `Z` action or that finite
corner boxes are exactly translation-reindexed.  A centered or bilateral
exhaustion, together with a new boundary comparison, is required.
-/

import YMGap.Continuum.Z4FiniteCylinderTimeTranslationColimit

namespace YMGap.Continuum.Z4CornerTimeTranslationObstruction

open YMGap.Continuum
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem timeShiftVertex_timeCoordinate
    (shift : Nat) (vertex : Z4Vertex) :
    (timeShiftVertex shift vertex).2.2.2 = vertex.2.2.2 + shift := by
  obtain ⟨a, b, c, d⟩ := vertex
  rfl

theorem v0_not_in_timeShiftVertex_range
    {shift : Nat} (hshift : 0 < shift) :
    ¬ ∃ source : Z4Vertex, timeShiftVertex shift source = v0 := by
  rintro ⟨⟨a, b, c, d⟩, heq⟩
  have htime := congrArg (fun vertex : Z4Vertex => vertex.2.2.2) heq
  simp only [timeShiftVertex, v0] at htime
  omega

theorem timeShiftVertex_not_surjective
    {shift : Nat} (hshift : 0 < shift) :
    ¬ Function.Surjective (timeShiftVertex shift) := by
  intro hsurjective
  exact v0_not_in_timeShiftVertex_range hshift (hsurjective v0)

theorem no_timeShiftVertex_rightInverse
    {shift : Nat} (hshift : 0 < shift) :
    ¬ ∃ inverse : Z4Vertex → Z4Vertex,
      ∀ vertex, timeShiftVertex shift (inverse vertex) = vertex := by
  rintro ⟨inverse, hinverse⟩
  exact v0_not_in_timeShiftVertex_range hshift
    ⟨inverse v0, hinverse v0⟩

def timeShiftBoxVertices (shift base : Nat) : List Z4Vertex :=
  (boxVertices base).map (timeShiftVertex shift)

theorem v0_not_mem_timeShiftBoxVertices
    {shift base : Nat} (hshift : 0 < shift) :
    v0 ∉ timeShiftBoxVertices shift base := by
  intro hmem
  obtain ⟨source, _, heq⟩ := List.mem_map.mp hmem
  exact v0_not_in_timeShiftVertex_range hshift ⟨source, heq⟩

theorem v0_mem_enlarged_boxVertices
    {shift base : Nat} (hshift : 0 < shift) :
    v0 ∈ boxVertices (base + shift) := by
  have hsize : 0 < base + shift := by omega
  unfold boxVertices v0
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr hsize, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr hsize, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨0, List.mem_range.mpr hsize, ?_⟩
  exact List.mem_map.mpr ⟨0, List.mem_range.mpr hsize, rfl⟩

private theorem mem_of_perm_reverse_local {A : Type} :
    ∀ {left right : List A}, left.Perm right →
      ∀ {item : A}, item ∈ right → item ∈ left
  | _, _, .nil, _, hitem => hitem
  | _, _, .cons head hperm, item, hitem => by
      rcases List.mem_cons.mp hitem with heq | htail
      · exact List.mem_cons.mpr (Or.inl heq)
      · exact List.mem_cons.mpr
          (Or.inr (mem_of_perm_reverse_local hperm htail))
  | _, _, .swap first second rest, item, hitem => by
      simp only [List.mem_cons] at hitem ⊢
      rcases hitem with heq | heq | hrest
      · exact Or.inr (Or.inl heq)
      · exact Or.inl heq
      · exact Or.inr (Or.inr hrest)
  | _, _, .trans hleft hright, item, hitem =>
      mem_of_perm_reverse_local hleft
        (mem_of_perm_reverse_local hright hitem)

/-- A positive shift of every old vertex cannot be a permutation of the full
enlarged corner box: the latter still contains the time-zero vertex. -/
theorem timeShiftBoxVertices_not_perm_enlarged
    {shift base : Nat} (hshift : 0 < shift) :
    ¬ (timeShiftBoxVertices shift base).Perm
      (boxVertices (base + shift)) := by
  intro hperm
  have hleft : v0 ∈ timeShiftBoxVertices shift base :=
    mem_of_perm_reverse_local hperm
      (v0_mem_enlarged_boxVertices hshift)
  exact v0_not_mem_timeShiftBoxVertices hshift hleft

#print axioms v0_not_in_timeShiftVertex_range
#print axioms timeShiftVertex_not_surjective
#print axioms no_timeShiftVertex_rightInverse
#print axioms v0_not_mem_timeShiftBoxVertices
#print axioms v0_mem_enlarged_boxVertices
#print axioms mem_of_perm_reverse_local
#print axioms timeShiftBoxVertices_not_perm_enlarged

end YMGap.Continuum.Z4CornerTimeTranslationObstruction
