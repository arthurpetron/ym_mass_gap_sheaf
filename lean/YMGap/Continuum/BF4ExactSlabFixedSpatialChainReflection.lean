/-
# Reflection geometry of the centered selected fixed-spatial chain

At even extent E=2*(radius+1), a chain with start+depth=radius+1 and
2*depth transitions has its actual selected face list preserved by the
existing physical face-ID reflection. Spatial faces retain both endpoints;
temporal faces use the required far-endpoint shift E-(time+1).

The lower/fixed/upper lists are the existing stable side partition, restricted
to this SAME chain. Reflection permutes its lower list onto its upper list;
the three lists together permute back to the whole selected action. No face
outside the fixed-width selection is added. Width containment is unnecessary
for this geometric closure: physical clipping is itself reflection invariant.

These are finite list identities for the original selected action. They do
not themselves establish reflection positivity, an OS Hilbert space, a
vacuum, a heat-cutoff limit, or a physical gap.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CayleyPruferInjection (nodup_map_of_injOn)
open YMGap.Continuum.Z4CanonicalPolymerUniverse (perm_of_nodup_mem_iff)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

/-- The original selected chain, with its final spatial slice included. -/
def selectedIds (radius width start depth : Nat) : List Nat :=
  chainIds (adjacentEvenExtent radius) width start (2*depth)

/-- Stable lower/fixed/upper partition of the original selected IDs. -/
def selectedParts (radius width start depth : Nat) : List Nat × List Nat × List Nat :=
  partitionBySide
    (fun id => adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id))
    (selectedIds radius width start depth)

def selectedLower (radius width start depth : Nat) : List Nat :=
  (selectedParts radius width start depth).1

def selectedFixed (radius width start depth : Nat) : List Nat :=
  (selectedParts radius width start depth).2.1

def selectedUpper (radius width start depth : Nat) : List Nat :=
  (selectedParts radius width start depth).2.2

theorem selectedLower_mem_iff {radius width start depth id : Nat} :
    id ∈ selectedLower radius width start depth ↔
      id ∈ selectedIds radius width start depth ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower :=
  mem_partitionBySide_lower _ _ _

theorem selectedFixed_mem_iff {radius width start depth id : Nat} :
    id ∈ selectedFixed radius width start depth ↔
      id ∈ selectedIds radius width start depth ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed :=
  mem_partitionBySide_fixed _ _ _

theorem selectedUpper_mem_iff {radius width start depth id : Nat} :
    id ∈ selectedUpper radius width start depth ↔
      id ∈ selectedIds radius width start depth ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .upper :=
  mem_partitionBySide_upper _ _ _

/-- Partitioning does not change the selected action or duplicate its
reflection-slice spatial factors. No centering guard is needed for this law. -/
theorem selectedParts_perm (radius width start depth : Nat) :
    (selectedLower radius width start depth ++
      selectedFixed radius width start depth ++
      selectedUpper radius width start depth).Perm
        (selectedIds radius width start depth) :=
  partitionBySide_perm _ _

private theorem selectedIds_nodup (radius width start depth : Nat) :
    (selectedIds radius width start depth).Nodup :=
  chainIds_nodup (adjacentEvenExtent radius) width start (2*depth)

private theorem selectedIds_physical {radius width start depth id : Nat}
    (hid : id ∈ selectedIds radius width start depth) :
    id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) :=
  chainIds_physical hid

/-- Reflection preserves the actual spatial selection and its centered
closed spatial / half-open temporal interval, including depth zero. -/
theorem selectedIds_reflect {radius width start depth id : Nat}
    (hcenter : start+depth = radius+1)
    (hid : id ∈ selectedIds radius width start depth) :
    slabFaceReflectId (adjacentEvenExtent radius) id ∈
      selectedIds radius width start depth := by
  obtain ⟨hphys, ha, hb, hc, hlo, hhi⟩ :=
    (chainIds_mem_iff (adjacentEvenExtent radius) width start (2*depth) id).mp hid
  apply (chainIds_mem_iff (adjacentEvenExtent radius) width start (2*depth) _).mpr
  refine ⟨slabFaceReflectId_physical hphys, ?_⟩
  rw [slabPlaquetteAt_slabFaceReflectId hphys]
  generalize hp : slabPlaquetteAt (adjacentEvenExtent radius) id = p at ha hb hc hlo hhi ⊢
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := p
  cases plane <;>
    simp only [timeReflectPlaquette, dirsOf, ne_eq, reduceCtorEq,
      not_false_eq_true, not_true_eq_false, true_and, false_and,
      or_false, false_or] at ha hb hc hlo hhi ⊢
  all_goals refine ⟨ha, hb, hc, ?_, ?_⟩
  all_goals unfold adjacentEvenExtent centralExtent; omega

/-- The membership equivalence is stated on physical IDs; no claim is
made about the numerical reflection's out-of-range fallback. -/
theorem selectedIds_reflect_iff {radius width start depth id : Nat}
    (hcenter : start+depth = radius+1)
    (hphys : id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius)) :
    slabFaceReflectId (adjacentEvenExtent radius) id ∈ selectedIds radius width start depth ↔
      id ∈ selectedIds radius width start depth := by
  constructor
  · intro h
    have hh := selectedIds_reflect hcenter h
    rw [slabFaceReflectId_involutive hphys] at hh
    exact hh
  · exact selectedIds_reflect hcenter

/-- The complete selected face list is permuted by the original reflection. -/
theorem selectedIds_reflection_perm {radius width start depth : Nat}
    (hcenter : start+depth = radius+1) :
    ((selectedIds radius width start depth).map
      (slabFaceReflectId (adjacentEvenExtent radius))).Perm
        (selectedIds radius width start depth) := by
  apply perm_of_nodup_mem_iff
  · exact nodup_map_of_injOn _ _ (selectedIds_nodup radius width start depth)
      (fun _ ha _ hb he => slabFaceReflectId_injective_on_physical
        (selectedIds_physical ha) (selectedIds_physical hb) he)
  · exact selectedIds_nodup radius width start depth
  · intro id
    constructor
    · intro h
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp h
      exact selectedIds_reflect hcenter hs
    · intro h
      exact List.mem_map.mpr ⟨slabFaceReflectId (adjacentEvenExtent radius) id,
        selectedIds_reflect hcenter h, slabFaceReflectId_involutive (selectedIds_physical h)⟩

/-- The selected lower action reflects onto exactly the selected upper
action. The list definitions are the same partitionBySide projections as
the generic selected-action interface, so no filter-equality transport is
needed by that consumer. -/
theorem selectedLower_reflection_perm {radius width start depth : Nat}
    (hcenter : start+depth = radius+1) :
    ((selectedLower radius width start depth).map
      (slabFaceReflectId (adjacentEvenExtent radius))).Perm
        (selectedUpper radius width start depth) := by
  have hn := (selectedParts_perm radius width start depth).nodup_iff.mpr
    (selectedIds_nodup radius width start depth)
  rw [List.append_assoc] at hn
  have hlower := (List.nodup_append.mp hn).1
  have hupper := (List.nodup_append.mp (List.nodup_append.mp hn).2.1).2.1
  apply perm_of_nodup_mem_iff
  · exact nodup_map_of_injOn _ _ hlower
      (fun _ ha _ hb he => slabFaceReflectId_injective_on_physical
        (selectedIds_physical (selectedLower_mem_iff.mp ha).1)
        (selectedIds_physical (selectedLower_mem_iff.mp hb).1) he)
  · exact hupper
  · intro id
    constructor
    · intro h
      obtain ⟨source, hs, rfl⟩ := List.mem_map.mp h
      obtain ⟨hselected, hside⟩ := selectedLower_mem_iff.mp hs
      apply selectedUpper_mem_iff.mpr
      refine ⟨selectedIds_reflect hcenter hselected, ?_⟩
      have hr := adjacentEvenSlabFaceReflectId_side (selectedIds_physical hselected)
      rw [hside] at hr
      exact hr
    · intro h
      obtain ⟨hselected, hside⟩ := selectedUpper_mem_iff.mp h
      have hsource : slabFaceReflectId (adjacentEvenExtent radius) id ∈
          selectedLower radius width start depth := by
        apply selectedLower_mem_iff.mpr
        refine ⟨selectedIds_reflect hcenter hselected, ?_⟩
        have hr := adjacentEvenSlabFaceReflectId_side (selectedIds_physical hselected)
        rw [hside] at hr
        exact hr
      exact List.mem_map.mpr ⟨slabFaceReflectId (adjacentEvenExtent radius) id,
        hsource, slabFaceReflectId_involutive (selectedIds_physical hselected)⟩

end YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedParts
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedLower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedFixed
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedUpper
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedLower_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedFixed_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedUpper_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedParts_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedIds_reflect
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedIds_reflect_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedIds_reflection_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainReflection.selectedLower_reflection_perm
