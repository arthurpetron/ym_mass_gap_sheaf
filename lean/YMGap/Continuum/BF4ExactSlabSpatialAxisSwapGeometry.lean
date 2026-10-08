/-
# Spatial x1/x2 swap of the SAME original finite slab

The fourth coordinate x3 remains physical time. The swap fixes x0 and x3,
preserves the literal width, every complete-slab face/link and the original
spatial, temporal and inclusive slice families. Time reflection commutes
with it. These are finite geometric identities only.

IMPORTANT: p12 is fixed as an UNORIENTED face but its canonical direction
order reverses. `swap_edgesOf_perm` concerns positive boundary incidence;
it does NOT assert equality of oriented plaquette words. That quaternion
word/character pin and the original reflected-form isometry are consumers,
not conclusions here. No spatial limit or continuum rotation is supplied.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
import YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier

namespace YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialTwoLayerBoundary (SliceLink)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier
  (baseLinks baseLinks_mem_iff baseLinks_nodup)

def swapVertex : Z4Vertex → Z4Vertex
  | (a,b,c,d) => (a,c,b,d)

def swapDir : Dir4 → Dir4
  | .x0 => .x0
  | .x1 => .x2
  | .x2 => .x1
  | .x3 => .x3

def swapPlane : Z4Plane → Z4Plane
  | .p01 => .p02
  | .p02 => .p01
  | .p03 => .p03
  | .p12 => .p12
  | .p13 => .p23
  | .p23 => .p13

def swapLink (link : Z4Link) : Z4Link := (swapVertex link.1, swapDir link.2)

def swapPlaquette (face : Z4Plaq) : Z4Plaq := (swapVertex face.1, swapPlane face.2)

theorem swapVertex_involutive (v : Z4Vertex) : swapVertex (swapVertex v) = v := by
  obtain ⟨a,b,c,d⟩ := v
  rfl

theorem swapDir_involutive (dir : Dir4) : swapDir (swapDir dir) = dir := by
  cases dir <;> rfl

theorem swapPlane_involutive (plane : Z4Plane) : swapPlane (swapPlane plane) = plane := by
  cases plane <;> rfl

theorem swapLink_involutive (link : Z4Link) : swapLink (swapLink link) = link := by
  obtain ⟨v,dir⟩ := link
  change (swapVertex (swapVertex v), swapDir (swapDir dir)) = (v,dir)
  rw [swapVertex_involutive, swapDir_involutive]

theorem swapPlaquette_involutive (face : Z4Plaq) :
    swapPlaquette (swapPlaquette face) = face := by
  obtain ⟨v,plane⟩ := face
  change (swapVertex (swapVertex v), swapPlane (swapPlane plane)) = (v,plane)
  rw [swapVertex_involutive, swapPlane_involutive]

theorem swapVertex_addE (v : Z4Vertex) (dir : Dir4) :
    swapVertex (addE v dir) = addE (swapVertex v) (swapDir dir) := by
  obtain ⟨a,b,c,d⟩ := v
  cases dir <;> rfl

/-- Canonical p12 order is reversed; incidence is nevertheless permuted. -/
theorem swap_edgesOf_perm (face : Z4Plaq) :
    ((edgesOf face).map swapLink).Perm (edgesOf (swapPlaquette face)) := by
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  cases plane <;> simp only [edgesOf, dirsOf, swapPlaquette, swapPlane,
    swapLink, swapVertex, swapDir, addE, List.map_cons, List.map_nil]
  all_goals first
    | exact List.Perm.refl _
    | exact (List.Perm.swap _ _ _).trans
        (List.Perm.cons _ (List.Perm.cons _ (List.Perm.swap _ _ [])))

theorem swapLink_mem_edgesOf {face : Z4Plaq} {link : Z4Link}
    (hl : link ∈ edgesOf face) : swapLink link ∈ edgesOf (swapPlaquette face) :=
  (swap_edgesOf_perm face).mem_iff.mp (List.mem_map.mpr ⟨link, hl, rfl⟩)

private theorem involution_perm {A : Type} [DecidableEq A]
    (f : A → A) (hf : ∀ a, f (f a) = a) (xs : List A)
    (hn : xs.Nodup) (hclosed : ∀ a, a ∈ xs → f a ∈ xs) :
    (xs.map f).Perm xs := by
  apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn f xs hn
    intro a _ b _ hab
    exact (hf a).symm.trans ((congrArg f hab).trans (hf b))
  · exact hn
  · intro a
    constructor
    · intro h
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h
      exact hclosed b hb
    · intro ha
      exact List.mem_map.mpr ⟨f a, hclosed a ha, hf a⟩

theorem swapPlaquette_mem_box_iff (face : Z4Plaq) (n : Nat) :
    swapPlaquette face ∈ boxPlaquettes n ↔ face ∈ boxPlaquettes n := by
  rw [mem_boxPlaquettes, mem_boxPlaquettes]
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  change (a<n ∧ c<n ∧ b<n ∧ d<n) ↔ (a<n ∧ b<n ∧ c<n ∧ d<n)
  constructor <;> rintro ⟨ha,hb,hc,hd⟩ <;> exact ⟨ha,hc,hb,hd⟩

theorem swapPlaquette_timeAdmissible_iff (extent : Nat) (face : Z4Plaq) :
    plaquetteTimeAdmissible extent (swapPlaquette face) ↔
      plaquetteTimeAdmissible extent face := by
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  cases plane <;> rfl

theorem swapPlaquette_mem_complete_iff (extent : Nat) (face : Z4Plaq) :
    swapPlaquette face ∈ boundaryCompleteSlabPlaquettes extent ↔
      face ∈ boundaryCompleteSlabPlaquettes extent := by
  rw [mem_boundaryCompleteSlabPlaquettes, mem_boundaryCompleteSlabPlaquettes]
  exact and_congr (swapPlaquette_mem_box_iff face (extent+1))
    (swapPlaquette_timeAdmissible_iff extent face)

theorem swap_completeSlabPlaquettes_perm (extent : Nat) :
    ((boundaryCompleteSlabPlaquettes extent).map swapPlaquette).Perm
      (boundaryCompleteSlabPlaquettes extent) :=
  involution_perm swapPlaquette swapPlaquette_involutive _
    (boundaryCompleteSlabPlaquettes_nodup extent)
    (fun face hf => (swapPlaquette_mem_complete_iff extent face).mpr hf)

theorem swapLink_mem_complete {extent : Nat} {link : Z4Link}
    (hl : link ∈ boundaryCompleteSlabLinks extent) :
    swapLink link ∈ boundaryCompleteSlabLinks extent := by
  obtain ⟨face, hf, he⟩ := (mem_boundaryCompleteSlabLinks_iff extent link).mp hl
  exact (mem_boundaryCompleteSlabLinks_iff extent (swapLink link)).mpr
    ⟨swapPlaquette face, (swapPlaquette_mem_complete_iff extent face).mpr hf,
      swapLink_mem_edgesOf he⟩

theorem swapLink_mem_complete_iff (extent : Nat) (link : Z4Link) :
    swapLink link ∈ boundaryCompleteSlabLinks extent ↔
      link ∈ boundaryCompleteSlabLinks extent := by
  constructor
  · intro h
    have hh := swapLink_mem_complete h
    simpa only [swapLink_involutive] using hh
  · exact swapLink_mem_complete

theorem swap_completeSlabLinks_perm (extent : Nat) :
    ((boundaryCompleteSlabLinks extent).map swapLink).Perm
      (boundaryCompleteSlabLinks extent) :=
  involution_perm swapLink swapLink_involutive _ (boundaryCompleteSlabLinks_nodup extent)
    (fun _ h => swapLink_mem_complete h)

private theorem swapDir_spatial (dir : Dir4) : swapDir dir ≠ .x3 ↔ dir ≠ .x3 := by
  cases dir <;> decide

private theorem swapPlane_spatial (plane : Z4Plane) :
    (dirsOf (swapPlane plane)).2 ≠ .x3 ↔ (dirsOf plane).2 ≠ .x3 := by
  cases plane <;> decide

private theorem swapPlane_temporal (plane : Z4Plane) :
    (dirsOf (swapPlane plane)).2 = .x3 ↔ (dirsOf plane).2 = .x3 := by
  cases plane <;> decide

theorem swapPlaquette_spatialFaces_mem_iff (width : Nat) (face : Z4Plaq) :
    swapPlaquette face ∈ spatialFaces width ↔ face ∈ spatialFaces width := by
  rw [spatialFaces_mem_iff, spatialFaces_mem_iff]
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  change (a<width ∧ c<width ∧ b<width ∧ d=0 ∧
    (dirsOf (swapPlane plane)).2 ≠ .x3) ↔
      (a<width ∧ b<width ∧ c<width ∧ d=0 ∧ (dirsOf plane).2 ≠ .x3)
  rw [swapPlane_spatial]
  constructor <;> rintro ⟨ha,hb,hc,hd,hp⟩ <;> exact ⟨ha,hc,hb,hd,hp⟩

theorem swapPlaquette_temporalFaces_mem_iff (width : Nat) (face : Z4Plaq) :
    swapPlaquette face ∈ temporalFaces width ↔ face ∈ temporalFaces width := by
  rw [temporalFaces_mem_iff, temporalFaces_mem_iff]
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  change (a<width ∧ c<width ∧ b<width ∧ d=0 ∧
    (dirsOf (swapPlane plane)).2 = .x3) ↔
      (a<width ∧ b<width ∧ c<width ∧ d=0 ∧ (dirsOf plane).2 = .x3)
  rw [swapPlane_temporal]
  constructor <;> rintro ⟨ha,hb,hc,hd,hp⟩ <;> exact ⟨ha,hc,hb,hd,hp⟩

theorem swap_spatialFaces_perm (width : Nat) :
    ((spatialFaces width).map swapPlaquette).Perm (spatialFaces width) :=
  involution_perm swapPlaquette swapPlaquette_involutive _ (spatialFaces_nodup width)
    (fun face hf => (swapPlaquette_spatialFaces_mem_iff width face).mpr hf)

theorem swap_temporalFaces_perm (width : Nat) :
    ((temporalFaces width).map swapPlaquette).Perm (temporalFaces width) :=
  involution_perm swapPlaquette swapPlaquette_involutive _ (temporalFaces_nodup width)
    (fun face hf => (swapPlaquette_temporalFaces_mem_iff width face).mpr hf)

theorem swapLink_sliceLink_iff (width time : Nat) (link : Z4Link) :
    SliceLink width time (swapLink link) ↔ SliceLink width time link := by
  obtain ⟨⟨a,b,c,d⟩,dir⟩ := link
  change (swapDir dir ≠ .x3 ∧ a≤width ∧ c≤width ∧ b≤width ∧ d=time) ↔
    (dir ≠ .x3 ∧ a≤width ∧ b≤width ∧ c≤width ∧ d=time)
  rw [swapDir_spatial]
  constructor <;> rintro ⟨hp,ha,hb,hc,ht⟩ <;> exact ⟨hp,ha,hc,hb,ht⟩

theorem swapLink_baseLinks_mem_iff (width : Nat) (link : Z4Link) :
    swapLink link ∈ baseLinks width ↔ link ∈ baseLinks width := by
  rw [baseLinks_mem_iff, baseLinks_mem_iff]
  exact swapLink_sliceLink_iff width 0 link

theorem swap_baseLinks_perm (width : Nat) :
    ((baseLinks width).map swapLink).Perm (baseLinks width) :=
  involution_perm swapLink swapLink_involutive _ (baseLinks_nodup width)
    (fun link hl => (swapLink_baseLinks_mem_iff width link).mpr hl)

theorem swapVertex_timeReflect_commute (extent : Nat) (v : Z4Vertex) :
    swapVertex (timeReflectVertex extent v) = timeReflectVertex extent (swapVertex v) := by
  obtain ⟨a,b,c,d⟩ := v
  rfl

theorem swapLink_timeReflect_commute (extent : Nat) (link : Z4Link) :
    swapLink (timeReflectLink extent link) = timeReflectLink extent (swapLink link) := by
  obtain ⟨⟨a,b,c,d⟩,dir⟩ := link
  cases dir <;> rfl

theorem swapPlaquette_timeReflect_commute (extent : Nat) (face : Z4Plaq) :
    swapPlaquette (timeReflectPlaquette extent face) =
      timeReflectPlaquette extent (swapPlaquette face) := by
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  cases plane <;> rfl

theorem swapLink_timeShift_commute (time : Nat) (link : Z4Link) :
    swapLink (timeShiftLink time link) = timeShiftLink time (swapLink link) := by
  obtain ⟨⟨a,b,c,d⟩,dir⟩ := link
  rfl

theorem swapPlaquette_timeShift_commute (time : Nat) (face : Z4Plaq) :
    swapPlaquette (timeShiftPlaquette time face) =
      timeShiftPlaquette time (swapPlaquette face) := by
  obtain ⟨⟨a,b,c,d⟩,plane⟩ := face
  rfl

end YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry

#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapVertex_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapDir_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlane_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_involutive
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapVertex_addE
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_edgesOf_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_mem_edgesOf
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_mem_box_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_timeAdmissible_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_mem_complete_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_completeSlabPlaquettes_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_mem_complete
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_mem_complete_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_completeSlabLinks_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_spatialFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_temporalFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_spatialFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_temporalFaces_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_sliceLink_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_baseLinks_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swap_baseLinks_perm
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapVertex_timeReflect_commute
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_timeReflect_commute
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_timeReflect_commute
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapLink_timeShift_commute
#print axioms YMGap.Continuum.BF4ExactSlabSpatialAxisSwapGeometry.swapPlaquette_timeShift_commute
