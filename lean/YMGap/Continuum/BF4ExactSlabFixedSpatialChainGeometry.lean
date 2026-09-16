/-
# Original face geometry for any finite number of fixed-spatial layers

A chain of n temporal layers contains the n+1 spatial slices and the n
intervening temporal layers, each exactly once. All identifiers belong to
the same original ambient slab. Containment gives the complete spatial-base
box and time interval; without containment the list remains the literal
clipped selection of physical faces.

The consumer is one common temporal sweep of this original finite action.
The width-only placed face list also supplies a permutation for its heat
products. No arbitrary-chain boundary-carrier or operator identification,
stationary normalization, quantitative estimate, or continuum limit is proved.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement

/-- The final spatial slice is included, and no intervening slice is repeated. -/
def chainIds (extent width start : Nat) : Nat → List Nat
  | 0 => spatialIds extent width start
  | steps+1 => spatialIds extent width start ++
      (temporalIds extent width start ++ chainIds extent width (start+1) steps)

/-- Explicit original finite-window membership, including the terminal slice. -/
theorem chainIds_mem_iff (extent width start steps id : Nat) :
    id ∈ chainIds extent width start steps ↔
      id ∈ slabPhysicalFaceEdges extent ∧
      (slabPlaquetteAt extent id).1.1 < width ∧
      (slabPlaquetteAt extent id).1.2.1 < width ∧
      (slabPlaquetteAt extent id).1.2.2.1 < width ∧
      start ≤ (slabPlaquetteAt extent id).1.2.2.2 ∧
      (((dirsOf (slabPlaquetteAt extent id).2).2 ≠ Dir4.x3 ∧
        (slabPlaquetteAt extent id).1.2.2.2 ≤ start+steps) ∨
       ((dirsOf (slabPlaquetteAt extent id).2).2 = Dir4.x3 ∧
        (slabPlaquetteAt extent id).1.2.2.2 < start+steps)) := by
  induction steps generalizing start with
  | zero =>
      rw [chainIds, spatialIds_mem_iff]
      constructor
      · rintro ⟨hi, ha, hb, hc, ht, hd⟩
        exact ⟨hi, ha, hb, hc, by omega, Or.inl ⟨hd, by omega⟩⟩
      · rintro ⟨hi, ha, hb, hc, hl, hs | ht⟩
        · exact ⟨hi, ha, hb, hc, by omega, hs.1⟩
        · have hfalse : False := by omega
          exact False.elim hfalse
  | succ steps ih =>
      rw [chainIds, List.mem_append, List.mem_append,
        spatialIds_mem_iff, temporalIds_mem_iff, ih]
      constructor
      · intro h
        rcases h with hs | ht | hr
        · obtain ⟨hi, ha, hb, hc, ht, hd⟩ := hs
          exact ⟨hi, ha, hb, hc, by omega, Or.inl ⟨hd, by omega⟩⟩
        · obtain ⟨hi, ha, hb, hc, ht, hd⟩ := ht
          exact ⟨hi, ha, hb, hc, by omega, Or.inr ⟨hd, by omega⟩⟩
        · obtain ⟨hi, ha, hb, hc, hl, hs | ht⟩ := hr
          · exact ⟨hi, ha, hb, hc, by omega, Or.inl ⟨hs.1, by omega⟩⟩
          · exact ⟨hi, ha, hb, hc, by omega, Or.inr ⟨ht.1, by omega⟩⟩
      · rintro ⟨hi, ha, hb, hc, hl, hr⟩
        by_cases he : (slabPlaquetteAt extent id).1.2.2.2 = start
        · rcases hr with hs | ht
          · exact Or.inl ⟨hi, ha, hb, hc, he, hs.1⟩
          · exact Or.inr (Or.inl ⟨hi, ha, hb, hc, he, ht.1⟩)
        · refine Or.inr (Or.inr ?_)
          refine ⟨hi, ha, hb, hc, by omega, ?_⟩
          rcases hr with hs | ht
          · exact Or.inl ⟨hs.1, by omega⟩
          · exact Or.inr ⟨ht.1, by omega⟩

theorem chainIds_physical {extent width start steps id : Nat}
    (hi : id ∈ chainIds extent width start steps) :
    id ∈ slabPhysicalFaceEdges extent :=
  ((chainIds_mem_iff extent width start steps id).mp hi).1

theorem chainIds_time_lower {extent width start steps id : Nat}
    (hi : id ∈ chainIds extent width start steps) :
    start ≤ (slabPlaquetteAt extent id).1.2.2.2 :=
  ((chainIds_mem_iff extent width start steps id).mp hi).2.2.2.2.1

/-- Duplicate-freeness records that every shared spatial weight occurs once. -/
theorem chainIds_nodup (extent width start steps : Nat) :
    (chainIds extent width start steps).Nodup := by
  induction steps generalizing start with
  | zero => exact spatialIds_nodup extent width start
  | succ steps ih =>
      change (spatialIds extent width start ++
        (temporalIds extent width start ++ chainIds extent width (start+1) steps)).Nodup
      refine List.nodup_append.mpr ⟨spatialIds_nodup extent width start,
        List.nodup_append.mpr ⟨temporalIds_nodup extent width start, ih (start+1), ?_⟩, ?_⟩
      · intro a ha b hb he
        subst b
        have ht := ((temporalIds_mem_iff extent width start a).mp ha).2.2.2.2.1
        have hl := chainIds_time_lower hb
        omega
      · intro a ha b hb he
        subst b
        have hs := (spatialIds_mem_iff extent width start a).mp ha
        rcases List.mem_append.mp hb with ht | hr
        · exact hs.2.2.2.2.2 ((temporalIds_mem_iff extent width start a).mp ht).2.2.2.2.2
        · have hl := chainIds_time_lower hr
          have ht := hs.2.2.2.2.1
          omega

theorem chainIds_faces_nodup (extent width start steps : Nat) :
    ((chainIds extent width start steps).map (slabPlaquetteAt extent)).Nodup :=
  CayleyPruferInjection.nodup_map_of_injOn _ _ (chainIds_nodup extent width start steps)
    (fun _ ha _ hb he => slabPlaquetteAt_injective_on_physical
      (chainIds_physical ha) (chainIds_physical hb) he)

/-- The existing two-layer face geometry is the literal two-step instance. -/
theorem chainIds_two (extent width start : Nat) :
    chainIds extent width start 2 = twoLayerIds extent width start := by
  simp only [chainIds, twoLayerIds, List.append_assoc, Nat.add_assoc]

/-- Under containment, every raw face in the stated window is present. -/
theorem chainIds_faces_mem_iff (extent width start steps : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent) (p : Z4Plaq) :
    p ∈ (chainIds extent width start steps).map (slabPlaquetteAt extent) ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      start ≤ p.1.2.2.2 ∧
      (((dirsOf p.2).2 ≠ Dir4.x3 ∧ p.1.2.2.2 ≤ start+steps) ∨
       ((dirsOf p.2).2 = Dir4.x3 ∧ p.1.2.2.2 < start+steps)) := by
  constructor
  · intro hp
    obtain ⟨id, hi, rfl⟩ := List.mem_map.mp hp
    exact ((chainIds_mem_iff extent width start steps id).mp hi).2
  · intro hp
    have hm : p ∈ boundaryCompleteSlabPlaquettes extent := by
      rcases hp.2.2.2.2 with hs | htemp
      · have hface := (spatialIds_faces_mem_iff extent width p.1.2.2.2 hw
          (show p.1.2.2.2 ≤ extent by omega) p).mpr
          ⟨hp.1, hp.2.1, hp.2.2.1, rfl, hs.1⟩
        obtain ⟨id, hi, he⟩ := List.mem_map.mp hface
        rw [← he]
        exact slabPlaquetteAt_mem ((spatialIds_mem_iff extent width p.1.2.2.2 id).mp hi).1
      · have hface := (temporalIds_faces_mem_iff extent width p.1.2.2.2 hw
          (show p.1.2.2.2+1 ≤ extent by omega) p).mpr
          ⟨hp.1, hp.2.1, hp.2.2.1, rfl, htemp.1⟩
        obtain ⟨id, hi, he⟩ := List.mem_map.mp hface
        rw [← he]
        exact slabPlaquetteAt_mem ((temporalIds_mem_iff extent width p.1.2.2.2 id).mp hi).1
    let id := listIndexOf p (boundaryCompleteSlabPlaquettes extent)
    have hi : id ∈ slabPhysicalFaceEdges extent :=
      List.mem_range.mpr (listIndexOf_lt_of_mem p _ hm)
    have he : slabPlaquetteAt extent id = p := getD_listIndexOf_of_mem _ _ _ hm
    refine List.mem_map.mpr ⟨id, (chainIds_mem_iff extent width start steps id).mpr ?_, he⟩
    exact ⟨hi, he.symm ▸ hp⟩

/-- A width-only sequence of placed canonical faces, with no ambient extent. -/
def chainFaces (width start : Nat) : Nat → List Z4Plaq
  | 0 => (spatialFaces width).map (timeShiftPlaquette start)
  | steps+1 => (spatialFaces width).map (timeShiftPlaquette start) ++
      ((temporalFaces width).map (timeShiftPlaquette start) ++
        chainFaces width (start+1) steps)

/-- Exact face-product reordering on the unchanged original ambient carrier. -/
theorem chainFaces_perm (extent width start steps : Nat)
    (hw : width ≤ extent+1) (ht : start+steps ≤ extent) :
    (chainFaces width start steps).Perm
      ((chainIds extent width start steps).map (slabPlaquetteAt extent)) := by
  induction steps generalizing start with
  | zero =>
      exact spatialFaces_shift_perm extent width start hw (by omega)
  | succ steps ih =>
      simp only [chainFaces, chainIds, List.map_append]
      exact (spatialFaces_shift_perm extent width start hw (by omega)).append
        ((temporalFaces_shift_perm extent width start hw (by omega)).append
          (ih (start+1) (by omega)))

theorem chainFaces_nodup (width start steps : Nat) :
    (chainFaces width start steps).Nodup :=
  (chainFaces_perm (width+start+steps) width start steps (by omega) (by omega)).nodup_iff.mpr
    (chainIds_faces_nodup (width+start+steps) width start steps)

theorem chainFaces_mem_iff (width start steps : Nat) (p : Z4Plaq) :
    p ∈ chainFaces width start steps ↔
      p.1.1 < width ∧ p.1.2.1 < width ∧ p.1.2.2.1 < width ∧
      start ≤ p.1.2.2.2 ∧
      (((dirsOf p.2).2 ≠ Dir4.x3 ∧ p.1.2.2.2 ≤ start+steps) ∨
       ((dirsOf p.2).2 = Dir4.x3 ∧ p.1.2.2.2 < start+steps)) :=
  (chainFaces_perm (width+start+steps) width start steps (by omega) (by omega)).mem_iff.trans
    (chainIds_faces_mem_iff (width+start+steps) width start steps (by omega) (by omega) p)

end YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_time_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_faces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_two
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainIds_faces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainFaces
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainFaces_nodup
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry.chainFaces_mem_iff
