/-
# Spatially recentered physical probe presentations

Translate the original spatial face words without changing coefficients or
distance from the reflection plane. A computed padding puts every actual
edge endpoint at a requested spatial margin. Radius and physical time advance
are preserved. These are geometric statements only: no equality of states,
completed norms, or expectations in different boxes is asserted.
-/

import YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabTemporalSweep (FaceFactor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (physicalTime)

def translateFactor (shift : Nat) (f : FaceFactor) : FaceFactor :=
  (shiftFace shift 0 f.1, f.2)

def translateSchedule (shift : Nat) (fs : List (Nat × List FaceFactor)) :
    List (Nat × List FaceFactor) :=
  fs.map (fun e => (e.1, e.2.map (translateFactor shift)))

def translateSpan (shift : Nat) (xs : DistanceSpan) : DistanceSpan :=
  xs.map (fun x => (x.1, translateSchedule shift x.2))

theorem shiftFace_spatial {width target shift : Nat}
    (hroom : width+shift ≤ target) {p : Z4Plaq} (hp : p ∈ spatialFaces width) :
    shiftFace shift 0 p ∈ spatialFaces target := by
  obtain ⟨⟨a, b, c, d⟩, plane⟩ := p
  have h := (spatialFaces_mem_iff width ((a, b, c, d), plane)).mp hp
  change a < width ∧ b < width ∧ c < width ∧ d = 0 ∧
    (dirsOf plane).2 ≠ Dir4.x3 at h
  apply (spatialFaces_mem_iff target _).mpr
  simp only [shiftFace, shiftVertex, Nat.add_zero]
  exact ⟨by omega, by omega, by omega, h.2.2.2.1, h.2.2.2.2⟩

theorem translateSpan_physical {width target shift : Nat}
    (hroom : width+shift ≤ target) (xs : DistanceSpan) (hx : Physical width xs) :
    Physical target (translateSpan shift xs) := by
  intro x hm e he f hf
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hm
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact shiftFace_spatial hroom (hx y hy d hd g hg)

theorem scheduleRadius_translate (shift : Nat) :
    (fs : List (Nat × List FaceFactor)) →
    scheduleRadius (translateSchedule shift fs) = scheduleRadius fs
  | [] => rfl
  | e::es => by
      change max e.1 (scheduleRadius (translateSchedule shift es)) =
        max e.1 (scheduleRadius es)
      rw [scheduleRadius_translate shift es]

theorem radius_translate (shift : Nat) : (xs : DistanceSpan) →
    radius (translateSpan shift xs) = radius xs
  | [] => rfl
  | x::xs => by
      change max (scheduleRadius (translateSchedule shift x.2))
        (radius (translateSpan shift xs)) = max (scheduleRadius x.2) (radius xs)
      rw [scheduleRadius_translate, radius_translate shift xs]

theorem translateSchedule_advance (shift n : Nat) (fs : List (Nat × List FaceFactor)) :
    translateSchedule shift (advanceSchedule n fs) =
      advanceSchedule n (translateSchedule shift fs) := by
  simp only [translateSchedule, advanceSchedule, List.map_map, Function.comp_def]

theorem translateSpan_advance (shift n : Nat) (xs : DistanceSpan) :
    translateSpan shift (advanceSpan n xs) = advanceSpan n (translateSpan shift xs) := by
  simp only [translateSpan, advanceSpan, List.map_map, Function.comp_def,
    translateSchedule_advance]

/-- One extra layer on each side accommodates all actual edge endpoints. -/
def paddedWidth (width margin : Nat) : Nat := width+2*margin+2

def recenter {width : Nat} (margin : Nat) (x : PhysicalSpan width) :
    PhysicalSpan (paddedWidth width margin) :=
  ⟨translateSpan (margin+1) x.val,
    translateSpan_physical (by unfold paddedWidth; omega) x.val x.property⟩

theorem recenter_radius {width : Nat} (margin : Nat) (x : PhysicalSpan width) :
    radius (recenter margin x).val = radius x.val := radius_translate _ _

theorem recenter_time {width : Nat} (margin n : Nat) (x : PhysicalSpan width) :
    recenter margin (physicalTime n x) = physicalTime n (recenter margin x) :=
  Subtype.ext (translateSpan_advance _ _ _)

/-- Distance from the six spatial boundary planes; time is unrestricted. -/
def SpatialInset (width margin : Nat) (v : Z4Vertex) : Prop :=
  margin ≤ v.1 ∧ v.1+margin ≤ width ∧
  margin ≤ v.2.1 ∧ v.2.1+margin ≤ width ∧
  margin ≤ v.2.2.1 ∧ v.2.2.1+margin ≤ width

theorem recenter_face_inset {width : Nat} (margin : Nat) {p : Z4Plaq}
    (hp : p ∈ spatialFaces width) {v : Z4Vertex}
    (hv : v ∈ boundaryVertices (shiftFace (margin+1) 0 p)) :
    SpatialInset (paddedWidth width margin) margin v := by
  rw [boundaryVertices_shiftFace] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  have hp' : p ∈ boundaryCompleteSlabPlaquettes width := by
    have h := spatialFaces_shift_physical (extent := width) (time := 0)
      (by omega) (by omega) hp
    simpa only [timeShiftPlaquette, Nat.add_zero] using h
  have hi := boundary_vertex_inset_zero hp' hu
  obtain ⟨a, b, c, d⟩ := u
  simp only [VertexInset, Nat.add_zero] at hi
  simp only [SpatialInset, paddedWidth, shiftVertex, Nat.add_zero]
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Every face actually occurring in the recentered signed presentation has
the requested endpoint margin, not merely its base vertex. -/
theorem recenter_inset {width : Nat} (margin : Nat) (x : PhysicalSpan width)
    (a : _ ) (ha : a ∈ (recenter margin x).val)
    (e : _) (he : e ∈ a.2) (f : FaceFactor) (hf : f ∈ e.2)
    {v : Z4Vertex} (hv : v ∈ boundaryVertices f.1) :
    SpatialInset (paddedWidth width margin) margin v := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact recenter_face_inset margin (x.property b hb d hd g hg) hv

end YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateFactor
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateSchedule
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateSpan
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.shiftFace_spatial
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateSpan_physical
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.scheduleRadius_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.radius_translate
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateSchedule_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.translateSpan_advance
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.paddedWidth
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.recenter
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.recenter_radius
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.recenter_time
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.SpatialInset
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.recenter_face_inset
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialSpatialRecenter.recenter_inset
