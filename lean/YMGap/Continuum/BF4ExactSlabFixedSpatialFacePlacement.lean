/-
# Width-only original face lists and their placement at any contained time

The canonical spatial and temporal faces are the original physical faces at
time zero in the source slab of extent width+1, restricted to spatial BASE
coordinates below width. Their time translates permute the existing original
face-ID lists in every ambient slab satisfying the displayed containment
guards. No face or character term is omitted or counted twice.

The consumer is the original spatial/kinetic heat-product pin on a fixed
spatial boundary carrier. These are finite geometric identities, not an
operator estimate, stationary-vacuum construction, or continuum conclusion.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
import YMGap.Continuum.BF4ExactSlabTimeEmbeddingGeometry
import YMGap.Continuum.Z4CanonicalPolymerUniverse
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry

/-- The original spatial faces, on a carrier depending only on width. -/
def spatialFaces (width : Nat) : List Z4Plaq :=
  (spatialIds (width+1) width 0).map (slabPlaquetteAt (width+1))

/-- The original temporal layer, on a carrier depending only on width. -/
def temporalFaces (width : Nat) : List Z4Plaq :=
  (temporalIds (width+1) width 0).map (slabPlaquetteAt (width+1))

theorem spatialIds_faces_mem_iff (extent width time : Nat)
    (hw : width ≤ extent+1) (ht : time ≤ extent) (p : Z4Plaq) :
    p ∈ (spatialIds extent width time).map (slabPlaquetteAt extent) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = time ∧ (dirsOf p.2).2 ≠ Dir4.x3 := by
  constructor
  · intro hp
    obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hp
    exact ((spatialIds_mem_iff extent width time id).mp hi).2
  · intro hp
    have hm : p ∈ boundaryCompleteSlabPlaquettes extent := by
      apply (mem_boundaryCompleteSlabPlaquettes extent p).mpr
      constructor
      · rw [mem_boxPlaquettes]
        exact ⟨Nat.lt_of_lt_of_le hp.1 hw, Nat.lt_of_lt_of_le hp.2.1 hw,
          Nat.lt_of_lt_of_le hp.2.2.1 hw, by omega⟩
      · obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
        have hd := hp.2.2.2.2
        have he := hp.2.2.2.1
        cases plane <;> simp only [dirsOf] at hd <;> try exact False.elim (hd rfl)
        all_goals change d ≤ extent
        all_goals dsimp only at he
        all_goals omega
    let id := listIndexOf p (boundaryCompleteSlabPlaquettes extent)
    have hi : id ∈ slabPhysicalFaceEdges extent :=
      List.mem_range.mpr (listIndexOf_lt_of_mem p _ hm)
    have he : slabPlaquetteAt extent id = p := getD_listIndexOf_of_mem _ _ _ hm
    refine List.mem_map.mpr ⟨id, (spatialIds_mem_iff extent width time id).mpr ?_, he⟩
    exact ⟨hi, he.symm ▸ hp⟩

theorem temporalIds_faces_mem_iff (extent width time : Nat)
    (hw : width ≤ extent+1) (ht : time+1 ≤ extent) (p : Z4Plaq) :
    p ∈ (temporalIds extent width time).map (slabPlaquetteAt extent) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = time ∧ (dirsOf p.2).2 = Dir4.x3 := by
  constructor
  · intro hp
    obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hp
    exact ((temporalIds_mem_iff extent width time id).mp hi).2
  · intro hp
    have hm : p ∈ boundaryCompleteSlabPlaquettes extent := by
      apply (mem_boundaryCompleteSlabPlaquettes extent p).mpr
      constructor
      · rw [mem_boxPlaquettes]
        exact ⟨Nat.lt_of_lt_of_le hp.1 hw, Nat.lt_of_lt_of_le hp.2.1 hw,
          Nat.lt_of_lt_of_le hp.2.2.1 hw, by omega⟩
      · obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
        have hd := hp.2.2.2.2
        have he := hp.2.2.2.1
        cases plane <;> simp only [dirsOf] at hd <;> try cases hd
        all_goals change d < extent
        all_goals dsimp only at he
        all_goals omega
    let id := listIndexOf p (boundaryCompleteSlabPlaquettes extent)
    have hi : id ∈ slabPhysicalFaceEdges extent :=
      List.mem_range.mpr (listIndexOf_lt_of_mem p _ hm)
    have he : slabPlaquetteAt extent id = p := getD_listIndexOf_of_mem _ _ _ hm
    refine List.mem_map.mpr ⟨id, (temporalIds_mem_iff extent width time id).mpr ?_, he⟩
    exact ⟨hi, he.symm ▸ hp⟩

theorem spatialFaces_mem_iff (width : Nat) (p : Z4Plaq) :
    p ∈ spatialFaces width ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = 0 ∧ (dirsOf p.2).2 ≠ Dir4.x3 :=
  spatialIds_faces_mem_iff (width+1) width 0 (by omega) (by omega) p

theorem temporalFaces_mem_iff (width : Nat) (p : Z4Plaq) :
    p ∈ temporalFaces width ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = 0 ∧ (dirsOf p.2).2 = Dir4.x3 :=
  temporalIds_faces_mem_iff (width+1) width 0 (by omega) (by omega) p

private theorem shift_faces_mem_iff (width time : Nat) (faces : List Z4Plaq)
    (planeProperty : Z4Plane → Prop)
    (hfaces : ∀ p, p ∈ faces ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = 0 ∧ planeProperty p.2) (p : Z4Plaq) :
    p ∈ faces.map (timeShiftPlaquette time) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = time ∧ planeProperty p.2 := by
  constructor
  · intro hp
    obtain ⟨⟨⟨a, b, c, d⟩, plane⟩, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨ha, hb, hc, hd, hplane⟩ := (hfaces _).mp hq
    change d = 0 at hd
    change a < width ∧ b < width ∧ c < width ∧ d+time = time ∧ planeProperty plane
    exact ⟨ha, hb, hc, by omega, hplane⟩
  · intro hp
    obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
    obtain ⟨ha, hb, hc, hd, hplane⟩ := hp
    refine List.mem_map.mpr ⟨((a, b, c, 0), plane), (hfaces _).mpr ?_, ?_⟩
    · exact ⟨ha, hb, hc, rfl, hplane⟩
    · change ((a, b, c, 0+time), plane) = ((a, b, c, d), plane)
      change d = time at hd
      rw [Nat.zero_add, hd]

theorem spatialFaces_shift_mem_iff (width time : Nat) (p : Z4Plaq) :
    p ∈ (spatialFaces width).map (timeShiftPlaquette time) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = time ∧ (dirsOf p.2).2 ≠ Dir4.x3 :=
  shift_faces_mem_iff width time (spatialFaces width)
    (fun plane => (dirsOf plane).2 ≠ Dir4.x3) (spatialFaces_mem_iff width) p

theorem temporalFaces_shift_mem_iff (width time : Nat) (p : Z4Plaq) :
    p ∈ (temporalFaces width).map (timeShiftPlaquette time) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      p.1.2.2.2 = time ∧ (dirsOf p.2).2 = Dir4.x3 :=
  shift_faces_mem_iff width time (temporalFaces width)
    (fun plane => (dirsOf plane).2 = Dir4.x3) (temporalFaces_mem_iff width) p

theorem spatialIds_nodup (extent width time : Nat) :
    (spatialIds extent width time).Nodup :=
  List.filter_sublist.nodup (List.filter_sublist.nodup (CayleyParentInj.range_nodup _))

theorem temporalIds_nodup (extent width time : Nat) :
    (temporalIds extent width time).Nodup :=
  List.filter_sublist.nodup (List.filter_sublist.nodup (CayleyParentInj.range_nodup _))

theorem spatialIds_faces_nodup (extent width time : Nat) :
    ((spatialIds extent width time).map (slabPlaquetteAt extent)).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) _
    (spatialIds_nodup extent width time)
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical
      ((spatialIds_mem_iff extent width time a).mp ha).1
      ((spatialIds_mem_iff extent width time b).mp hb).1 he)

theorem temporalIds_faces_nodup (extent width time : Nat) :
    ((temporalIds extent width time).map (slabPlaquetteAt extent)).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn (slabPlaquetteAt extent) _
    (temporalIds_nodup extent width time)
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical
      ((temporalIds_mem_iff extent width time a).mp ha).1
      ((temporalIds_mem_iff extent width time b).mp hb).1 he)

theorem spatialFaces_nodup (width : Nat) : (spatialFaces width).Nodup :=
  spatialIds_faces_nodup (width+1) width 0

theorem temporalFaces_nodup (width : Nat) : (temporalFaces width).Nodup :=
  temporalIds_faces_nodup (width+1) width 0

theorem spatialFaces_shift_nodup (width time : Nat) :
    ((spatialFaces width).map (timeShiftPlaquette time)).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (spatialFaces_nodup width)
    (fun _ _ _ _ he => BF4ExactSlabTimeEmbeddingGeometry.shift_injective time he)

theorem temporalFaces_shift_nodup (width time : Nat) :
    ((temporalFaces width).map (timeShiftPlaquette time)).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (temporalFaces_nodup width)
    (fun _ _ _ _ he => BF4ExactSlabTimeEmbeddingGeometry.shift_injective time he)

/-- Every canonical spatial factor occurs exactly once in the ambient slice. -/
theorem spatialFaces_shift_perm (extent width time : Nat)
    (hw : width ≤ extent+1) (ht : time ≤ extent) :
    ((spatialFaces width).map (timeShiftPlaquette time)).Perm
      ((spatialIds extent width time).map (slabPlaquetteAt extent)) :=
  Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    (spatialFaces_shift_nodup width time) (spatialIds_faces_nodup extent width time)
    (fun p => (spatialFaces_shift_mem_iff width time p).trans
      (spatialIds_faces_mem_iff extent width time hw ht p).symm)

/-- Every canonical temporal factor occurs exactly once in the ambient layer. -/
theorem temporalFaces_shift_perm (extent width time : Nat)
    (hw : width ≤ extent+1) (ht : time+1 ≤ extent) :
    ((temporalFaces width).map (timeShiftPlaquette time)).Perm
      ((temporalIds extent width time).map (slabPlaquetteAt extent)) :=
  Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff _ _
    (temporalFaces_shift_nodup width time) (temporalIds_faces_nodup extent width time)
    (fun p => (temporalFaces_shift_mem_iff width time p).trans
      (temporalIds_faces_mem_iff extent width time hw ht p).symm)

theorem spatialFaces_shift_physical {extent width time : Nat}
    (hw : width ≤ extent+1) (ht : time ≤ extent) {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) :
    timeShiftPlaquette time p ∈ boundaryCompleteSlabPlaquettes extent := by
  have hm := (spatialFaces_shift_perm extent width time hw ht).mem_iff.mp
    (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨id, hi, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact slabPlaquetteAt_mem ((spatialIds_mem_iff extent width time id).mp hi).1

theorem temporalFaces_shift_physical {extent width time : Nat}
    (hw : width ≤ extent+1) (ht : time+1 ≤ extent) {p : Z4Plaq}
    (hp : p ∈ temporalFaces width) :
    timeShiftPlaquette time p ∈ boundaryCompleteSlabPlaquettes extent := by
  have hm := (temporalFaces_shift_perm extent width time hw ht).mem_iff.mp
    (List.mem_map.mpr ⟨p, hp, rfl⟩)
  obtain ⟨id, hi, he⟩ := List.mem_map.mp hm
  rw [← he]
  exact slabPlaquetteAt_mem ((temporalIds_mem_iff extent width time id).mp hi).1

end YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialIds_faces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalIds_faces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_shift_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_shift_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialIds_faces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalIds_faces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_shift_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_shift_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_shift_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_shift_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.spatialFaces_shift_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement.temporalFaces_shift_physical
