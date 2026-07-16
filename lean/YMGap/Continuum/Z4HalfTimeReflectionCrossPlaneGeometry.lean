/-
# Cross-plane decomposition for the corrected Z4 reflection slab

For the odd corrected-slab extent `2h+1`, this file classifies every face and
actual link as strictly below the reflection plane, fixed by the plane, or
strictly above it.  The classification is geometric: spatial cells on time
slice `h` belong to the lower half, while time-oriented cells based at `h`
are the fixed cross-plane cells.

The output is deliberately prior to positivity.  It supplies exact finite
list partitions, proves that reflection exchanges the two open halves while
fixing the interface, and proves the incidence-locality statements needed to
split a spin-foam summand into lower, interface, and upper factors.
-/

import YMGap.Continuum.Z4HalfTimeReflectionPartition
import YMGap.Continuum.Z4FusionChannelConvolution

namespace YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Geometric side classifications -/

inductive CrossPlaneSide
  | lower
  | fixed
  | upper
  deriving DecidableEq

def flipSide : CrossPlaneSide -> CrossPlaneSide
  | .lower => .upper
  | .fixed => .fixed
  | .upper => .lower

def spatialHalfSide (half time : Nat) : CrossPlaneSide :=
  if time <= half then .lower else .upper

def temporalHalfSide (half time : Nat) : CrossPlaneSide :=
  if time < half then .lower
  else if time = half then .fixed else .upper

/-- Spatial plaquettes on the lower central slice belong to the lower half;
time-oriented plaquettes based there cross the reflection plane and are
fixed. -/
def plaquetteHalfSide (half : Nat) : Z4Plaq -> CrossPlaneSide
  | ((_, _, _, time), .p01)
  | ((_, _, _, time), .p02)
  | ((_, _, _, time), .p12) =>
      spatialHalfSide half time
  | ((_, _, _, time), .p03)
  | ((_, _, _, time), .p13)
  | ((_, _, _, time), .p23) =>
      temporalHalfSide half time

/-- Spatial links on the lower central slice belong to the lower half;
positive-time links based there cross the reflection plane and are fixed. -/
def linkHalfSide (half : Nat) : Z4Link -> CrossPlaneSide
  | ((_, _, _, time), .x0)
  | ((_, _, _, time), .x1)
  | ((_, _, _, time), .x2) =>
      spatialHalfSide half time
  | ((_, _, _, time), .x3) =>
      temporalHalfSide half time

theorem flipSide_involutive (side : CrossPlaneSide) :
    flipSide (flipSide side) = side := by
  cases side <;> rfl

private theorem spatialHalfSide_reflection
    {half time : Nat} (hadmissible : time <= half + half + 1) :
    spatialHalfSide half (half + half + 1 - time) =
      flipSide (spatialHalfSide half time) := by
  by_cases hlower : time <= half
  · have hreflected : half < half + half + 1 - time := by omega
    simp [spatialHalfSide, flipSide, hlower,
      Nat.not_le.mpr hreflected]
  · have htime : half < time := Nat.lt_of_not_ge hlower
    have hreflected : half + half + 1 - time <= half := by omega
    simp [spatialHalfSide, flipSide, hlower, hreflected]

private theorem temporalHalfSide_reflection
    {half time : Nat} (hadmissible : time < half + half + 1) :
    temporalHalfSide half (half + half - time) =
      flipSide (temporalHalfSide half time) := by
  by_cases hlower : time < half
  · have hreflectedLower : ¬ (half + half - time < half) := by omega
    have hreflectedFixed : half + half - time ≠ half := by omega
    simp [temporalHalfSide, flipSide, hlower,
      hreflectedLower, hreflectedFixed]
  · by_cases hfixed : time = half
    · subst time
      simp [temporalHalfSide, flipSide]
    · have hupper : half < time := by omega
      have hreflectedLower : half + half - time < half := by omega
      simp [temporalHalfSide, flipSide, hlower, hfixed,
        hreflectedLower]

theorem plaquetteHalfSide_reflection
    {half : Nat} {plaquette : Z4Plaq}
    (hadmissible : plaquetteTimeAdmissible
      (centralExtent half) plaquette) :
    plaquetteHalfSide half
        (timeReflectPlaquette (centralExtent half) plaquette) =
      flipSide (plaquetteHalfSide half plaquette) := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane
  · exact spatialHalfSide_reflection (by
      simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible)
  · exact spatialHalfSide_reflection (by
      simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible)
  · simpa [plaquetteHalfSide, timeReflectPlaquette, centralExtent] using
      (temporalHalfSide_reflection (half := half) (time := time) (by
        simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible))
  · exact spatialHalfSide_reflection (by
      simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible)
  · simpa [plaquetteHalfSide, timeReflectPlaquette, centralExtent] using
      (temporalHalfSide_reflection (half := half) (time := time) (by
        simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible))
  · simpa [plaquetteHalfSide, timeReflectPlaquette, centralExtent] using
      (temporalHalfSide_reflection (half := half) (time := time) (by
        simpa [plaquetteTimeAdmissible, centralExtent] using hadmissible))

theorem linkHalfSide_reflection
    {half : Nat} {link : Z4Link}
    (hadmissible : linkTimeAdmissible (centralExtent half) link) :
    linkHalfSide half (timeReflectLink (centralExtent half) link) =
      flipSide (linkHalfSide half link) := by
  obtain ⟨⟨a, b, c, time⟩, direction⟩ := link
  cases direction
  · exact spatialHalfSide_reflection (by
      simpa [linkTimeAdmissible, centralExtent] using hadmissible)
  · exact spatialHalfSide_reflection (by
      simpa [linkTimeAdmissible, centralExtent] using hadmissible)
  · exact spatialHalfSide_reflection (by
      simpa [linkTimeAdmissible, centralExtent] using hadmissible)
  · simpa [linkHalfSide, timeReflectLink, centralExtent] using
      (temporalHalfSide_reflection (half := half) (time := time) (by
        simpa [linkTimeAdmissible, centralExtent] using hadmissible))

/-! ## 2. A constructive three-way finite-list partition -/

/-- Stable three-way partition, with output ordered lower/fixed/upper. -/
def partitionBySide {A : Type} (side : A -> CrossPlaneSide) :
    List A -> List A × List A × List A
  | [] => ([], [], [])
  | head :: tail =>
      let parts := partitionBySide side tail
      match side head with
      | .lower => (head :: parts.1, parts.2.1, parts.2.2)
      | .fixed => (parts.1, head :: parts.2.1, parts.2.2)
      | .upper => (parts.1, parts.2.1, head :: parts.2.2)

theorem partitionBySide_perm {A : Type} (side : A -> CrossPlaneSide) :
    ∀ xs : List A,
      ((partitionBySide side xs).1 ++
        (partitionBySide side xs).2.1 ++
        (partitionBySide side xs).2.2).Perm xs
  | [] => List.Perm.nil
  | head :: tail => by
      have ih := partitionBySide_perm side tail
      cases hside : side head <;>
        simp only [partitionBySide, hside]
      · exact List.Perm.cons head ih
      · have hmove :
            ((partitionBySide side tail).1 ++ head ::
                ((partitionBySide side tail).2.1 ++
                  (partitionBySide side tail).2.2)).Perm
              (head :: ((partitionBySide side tail).1 ++
                ((partitionBySide side tail).2.1 ++
                  (partitionBySide side tail).2.2))) :=
            List.perm_middle
        have ih' :
            ((partitionBySide side tail).1 ++
              ((partitionBySide side tail).2.1 ++
                (partitionBySide side tail).2.2)).Perm tail := by
          simpa only [List.append_assoc] using ih
        simpa only [List.append_assoc] using
          hmove.trans (List.Perm.cons head ih')
      · have hmove :
            (((partitionBySide side tail).1 ++
                (partitionBySide side tail).2.1) ++ head ::
                  (partitionBySide side tail).2.2).Perm
              (head :: (((partitionBySide side tail).1 ++
                (partitionBySide side tail).2.1) ++
                  (partitionBySide side tail).2.2)) :=
            List.perm_middle
        have ih' :
            (((partitionBySide side tail).1 ++
              (partitionBySide side tail).2.1) ++
                (partitionBySide side tail).2.2).Perm tail := by
          simpa only [List.append_assoc] using ih
        simpa only [List.append_assoc] using
          hmove.trans (List.Perm.cons head ih')

def centralSlabFaceIdParts (half : Nat) :
    List Nat × List Nat × List Nat :=
  partitionBySide
    (fun id => plaquetteHalfSide half
      (slabPlaquetteAt (centralExtent half) id))
    (slabPhysicalFaceEdges (centralExtent half))

def centralSlabLinkParts (half : Nat) :
    List Z4Link × List Z4Link × List Z4Link :=
  partitionBySide (linkHalfSide half)
    (boundaryCompleteSlabLinks (centralExtent half))

theorem centralSlabFaceIdParts_perm (half : Nat) :
    ((centralSlabFaceIdParts half).1 ++
      (centralSlabFaceIdParts half).2.1 ++
      (centralSlabFaceIdParts half).2.2).Perm
      (slabPhysicalFaceEdges (centralExtent half)) := by
  exact partitionBySide_perm _ _

theorem centralSlabLinkParts_perm (half : Nat) :
    ((centralSlabLinkParts half).1 ++
      (centralSlabLinkParts half).2.1 ++
      (centralSlabLinkParts half).2.2).Perm
      (boundaryCompleteSlabLinks (centralExtent half)) := by
  exact partitionBySide_perm _ _

/-! ## 3. Numerical face reflection and side exchange -/

theorem slabFaceReflectId_side
    {half id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half)
          (slabFaceReflectId (centralExtent half) id)) =
      flipSide (plaquetteHalfSide half
        (slabPlaquetteAt (centralExtent half) id)) := by
  rw [slabPlaquetteAt_slabFaceReflectId hid]
  apply plaquetteHalfSide_reflection
  exact ((mem_boundaryCompleteSlabPlaquettes _ _).mp
    (slabPlaquetteAt_mem hid)).2

theorem centralSlabLink_reflection_side
    {half : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks (centralExtent half)) :
    linkHalfSide half (timeReflectLink (centralExtent half) link) =
      flipSide (linkHalfSide half link) := by
  apply linkHalfSide_reflection
  exact linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hlink

/-! ## 4. Cross-plane incidence locality -/

theorem lower_link_incident_face_ne_upper
    {half : Nat} {link : Z4Link} {plaquette : Z4Plaq}
    (hlinkSide : linkHalfSide half link = .lower)
    (hincidence : link ∈ edgesOf plaquette) :
    plaquetteHalfSide half plaquette ≠ .upper := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil,
    or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals cases plane
  all_goals simp only [dirsOf, addE, linkHalfSide,
    plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hlinkSide ⊢
  all_goals repeat' split at hlinkSide
  all_goals repeat' split
  all_goals simp_all
  all_goals omega

theorem fixed_link_incident_face_fixed
    {half : Nat} {link : Z4Link} {plaquette : Z4Plaq}
    (hlinkSide : linkHalfSide half link = .fixed)
    (hincidence : link ∈ edgesOf plaquette) :
    plaquetteHalfSide half plaquette = .fixed := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil,
    or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals cases plane
  all_goals simp only [dirsOf, addE, linkHalfSide,
    plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hlinkSide ⊢
  all_goals repeat' split at hlinkSide
  all_goals repeat' split
  all_goals simp_all
  all_goals omega

theorem upper_link_incident_face_ne_lower
    {half : Nat} {link : Z4Link} {plaquette : Z4Plaq}
    (hlinkSide : linkHalfSide half link = .upper)
    (hincidence : link ∈ edgesOf plaquette) :
    plaquetteHalfSide half plaquette ≠ .lower := by
  simp only [edgesOf, List.mem_cons, List.not_mem_nil,
    or_false] at hincidence
  rcases hincidence with rfl | rfl | rfl | rfl
  all_goals obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  all_goals cases plane
  all_goals simp only [dirsOf, addE, linkHalfSide,
    plaquetteHalfSide, spatialHalfSide, temporalHalfSide] at hlinkSide ⊢
  all_goals repeat' split at hlinkSide
  all_goals repeat' split
  all_goals simp_all
  all_goals omega

end YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.plaquetteHalfSide_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.linkHalfSide_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.partitionBySide_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.centralSlabFaceIdParts_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.centralSlabLinkParts_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.slabFaceReflectId_side
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.lower_link_incident_face_ne_upper
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.fixed_link_incident_face_fixed
#print axioms YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry.upper_link_incident_face_ne_lower
