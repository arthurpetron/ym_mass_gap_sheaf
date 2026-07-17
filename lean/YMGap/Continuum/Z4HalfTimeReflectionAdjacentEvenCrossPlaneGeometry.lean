/-
# Cross-plane geometry for the adjacent even reflection slab

One-step exchange uses the even reflection extent `2(r+1)`.  This file builds
the corresponding lower/fixed/upper classification independently of the
existing odd carrier.  Spatial plaquettes and links on the integer reflection
slice are fixed; time-oriented cells are exchanged across it.

The final local incidence calculation is load-bearing: a fixed spatial link
is incident to both a lower and an upper temporal plaquette.  Consequently
the old odd-carrier factorization, whose fixed links see only fixed faces,
cannot be reused.  An adjacent-even positive kernel must split that local
fusion multiplicity through explicit interface channels.
-/

import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Even-plane side classifiers -/

def adjacentEvenCenter (radius : Nat) : Nat := radius + 1

def adjacentEvenExtent (radius : Nat) : Nat :=
  centralExtent radius + 1

def adjacentEvenSpatialSide (radius time : Nat) : CrossPlaneSide :=
  if time < adjacentEvenCenter radius then .lower
  else if time = adjacentEvenCenter radius then .fixed else .upper

def adjacentEvenTemporalSide (radius time : Nat) : CrossPlaneSide :=
  if time < adjacentEvenCenter radius then .lower else .upper

def adjacentEvenPlaquetteSide (radius : Nat) : Z4Plaq → CrossPlaneSide
  | ((_, _, _, time), .p01)
  | ((_, _, _, time), .p02)
  | ((_, _, _, time), .p12) =>
      adjacentEvenSpatialSide radius time
  | ((_, _, _, time), .p03)
  | ((_, _, _, time), .p13)
  | ((_, _, _, time), .p23) =>
      adjacentEvenTemporalSide radius time

def adjacentEvenLinkSide (radius : Nat) : Z4Link → CrossPlaneSide
  | ((_, _, _, time), .x0)
  | ((_, _, _, time), .x1)
  | ((_, _, _, time), .x2) =>
      adjacentEvenSpatialSide radius time
  | ((_, _, _, time), .x3) =>
      adjacentEvenTemporalSide radius time

private theorem adjacentEvenSpatialSide_reflection
    {radius time : Nat} (hadmissible : time ≤ adjacentEvenExtent radius) :
    adjacentEvenSpatialSide radius (adjacentEvenExtent radius - time) =
      flipSide (adjacentEvenSpatialSide radius time) := by
  by_cases hlower : time < adjacentEvenCenter radius
  · have hreflectedUpper : adjacentEvenCenter radius <
        adjacentEvenExtent radius - time := by
      unfold adjacentEvenCenter adjacentEvenExtent centralExtent at *
      omega
    simp [adjacentEvenSpatialSide, hlower, flipSide,
      Nat.not_lt.mpr (Nat.le_of_lt hreflectedUpper),
      Nat.ne_of_gt hreflectedUpper]
  · by_cases hfixed : time = adjacentEvenCenter radius
    · subst time
      have hreflected : adjacentEvenExtent radius -
          adjacentEvenCenter radius = adjacentEvenCenter radius := by
        unfold adjacentEvenCenter adjacentEvenExtent centralExtent
        omega
      rw [hreflected]
      simp [adjacentEvenSpatialSide, flipSide]
    · have hupper : adjacentEvenCenter radius < time := by omega
      have hreflectedLower : adjacentEvenExtent radius - time <
          adjacentEvenCenter radius := by
        unfold adjacentEvenCenter adjacentEvenExtent centralExtent at *
        omega
      simp [adjacentEvenSpatialSide, hlower, hfixed, flipSide,
        hreflectedLower]

private theorem adjacentEvenTemporalSide_reflection
    {radius time : Nat} (hadmissible : time < adjacentEvenExtent radius) :
    adjacentEvenTemporalSide radius
        (adjacentEvenExtent radius - (time + 1)) =
      flipSide (adjacentEvenTemporalSide radius time) := by
  by_cases hlower : time < adjacentEvenCenter radius
  · have hreflectedUpper : adjacentEvenCenter radius ≤
        adjacentEvenExtent radius - (time + 1) := by
      unfold adjacentEvenCenter adjacentEvenExtent centralExtent at *
      omega
    simp [adjacentEvenTemporalSide, hlower, flipSide,
      Nat.not_lt.mpr hreflectedUpper]
  · have hupper : adjacentEvenCenter radius ≤ time := Nat.le_of_not_gt hlower
    have hreflectedLower : adjacentEvenExtent radius - (time + 1) <
        adjacentEvenCenter radius := by
      unfold adjacentEvenCenter adjacentEvenExtent centralExtent at *
      omega
    simp [adjacentEvenTemporalSide, hlower, flipSide, hreflectedLower]

theorem adjacentEvenPlaquetteSide_reflection
    {radius : Nat} {plaquette : Z4Plaq}
    (hadmissible : plaquetteTimeAdmissible
      (adjacentEvenExtent radius) plaquette) :
    adjacentEvenPlaquetteSide radius
        (timeReflectPlaquette (adjacentEvenExtent radius) plaquette) =
      flipSide (adjacentEvenPlaquetteSide radius plaquette) := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [plaquetteTimeAdmissible] using hadmissible)
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [plaquetteTimeAdmissible] using hadmissible)
  · simpa [adjacentEvenPlaquetteSide, timeReflectPlaquette] using
      (adjacentEvenTemporalSide_reflection
        (radius := radius) (time := time) (by
          simpa [plaquetteTimeAdmissible] using hadmissible))
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [plaquetteTimeAdmissible] using hadmissible)
  · simpa [adjacentEvenPlaquetteSide, timeReflectPlaquette] using
      (adjacentEvenTemporalSide_reflection
        (radius := radius) (time := time) (by
          simpa [plaquetteTimeAdmissible] using hadmissible))
  · simpa [adjacentEvenPlaquetteSide, timeReflectPlaquette] using
      (adjacentEvenTemporalSide_reflection
        (radius := radius) (time := time) (by
          simpa [plaquetteTimeAdmissible] using hadmissible))

theorem adjacentEvenLinkSide_reflection
    {radius : Nat} {link : Z4Link}
    (hadmissible : linkTimeAdmissible
      (adjacentEvenExtent radius) link) :
    adjacentEvenLinkSide radius
        (timeReflectLink (adjacentEvenExtent radius) link) =
      flipSide (adjacentEvenLinkSide radius link) := by
  obtain ⟨⟨a, b, c, time⟩, direction⟩ := link
  cases direction
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [linkTimeAdmissible] using hadmissible)
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [linkTimeAdmissible] using hadmissible)
  · exact adjacentEvenSpatialSide_reflection (by
      simpa [linkTimeAdmissible] using hadmissible)
  · simpa [adjacentEvenLinkSide, timeReflectLink] using
      (adjacentEvenTemporalSide_reflection
        (radius := radius) (time := time) (by
          simpa [linkTimeAdmissible] using hadmissible))

/-! ## 2. Exact finite partitions and reflection exchange -/

def adjacentEvenSlabFaceIdParts (radius : Nat) :
    List Nat × List Nat × List Nat :=
  partitionBySide
    (fun id => adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id))
    (slabPhysicalFaceEdges (adjacentEvenExtent radius))

def adjacentEvenSlabLinkParts (radius : Nat) :
    List Z4Link × List Z4Link × List Z4Link :=
  partitionBySide (adjacentEvenLinkSide radius)
    (boundaryCompleteSlabLinks (adjacentEvenExtent radius))

theorem adjacentEvenSlabFaceIdParts_perm (radius : Nat) :
    ((adjacentEvenSlabFaceIdParts radius).1 ++
      (adjacentEvenSlabFaceIdParts radius).2.1 ++
      (adjacentEvenSlabFaceIdParts radius).2.2).Perm
        (slabPhysicalFaceEdges (adjacentEvenExtent radius)) :=
  partitionBySide_perm _ _

theorem adjacentEvenSlabLinkParts_perm (radius : Nat) :
    ((adjacentEvenSlabLinkParts radius).1 ++
      (adjacentEvenSlabLinkParts radius).2.1 ++
      (adjacentEvenSlabLinkParts radius).2.2).Perm
        (boundaryCompleteSlabLinks (adjacentEvenExtent radius)) :=
  partitionBySide_perm _ _

theorem adjacentEvenSlabFaceReflectId_side
    {radius id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges
      (adjacentEvenExtent radius)) :
    adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius)
          (slabFaceReflectId (adjacentEvenExtent radius) id)) =
      flipSide (adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id)) := by
  rw [slabPlaquetteAt_slabFaceReflectId hid]
  apply adjacentEvenPlaquetteSide_reflection
  exact ((mem_boundaryCompleteSlabPlaquettes _ _).mp
    (slabPlaquetteAt_mem hid)).2

theorem adjacentEvenSlabLink_reflection_side
    {radius : Nat} {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks
      (adjacentEvenExtent radius)) :
    adjacentEvenLinkSide radius
        (timeReflectLink (adjacentEvenExtent radius) link) =
      flipSide (adjacentEvenLinkSide radius link) :=
  adjacentEvenLinkSide_reflection
    (linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hlink)

/-! ## 3. Fixed-link coupling obstruction to the old factorization -/

def adjacentEvenFixedSpatialLink (radius : Nat) : Z4Link :=
  (((0, 0, 0, radius + 1), .x0) : Z4Link)

def adjacentEvenLowerTemporalPlaquette (radius : Nat) : Z4Plaq :=
  (((0, 0, 0, radius), .p03) : Z4Plaq)

def adjacentEvenUpperTemporalPlaquette (radius : Nat) : Z4Plaq :=
  (((0, 0, 0, radius + 1), .p03) : Z4Plaq)

theorem adjacentEvenFixedSpatialLink_side (radius : Nat) :
    adjacentEvenLinkSide radius
      (adjacentEvenFixedSpatialLink radius) = .fixed := by
  simp [adjacentEvenLinkSide, adjacentEvenSpatialSide,
    adjacentEvenCenter, adjacentEvenFixedSpatialLink]

theorem adjacentEvenLowerTemporalPlaquette_side (radius : Nat) :
    adjacentEvenPlaquetteSide radius
      (adjacentEvenLowerTemporalPlaquette radius) = .lower := by
  simp [adjacentEvenPlaquetteSide, adjacentEvenTemporalSide,
    adjacentEvenCenter, adjacentEvenLowerTemporalPlaquette]

theorem adjacentEvenUpperTemporalPlaquette_side (radius : Nat) :
    adjacentEvenPlaquetteSide radius
      (adjacentEvenUpperTemporalPlaquette radius) = .upper := by
  simp [adjacentEvenPlaquetteSide, adjacentEvenTemporalSide,
    adjacentEvenCenter, adjacentEvenUpperTemporalPlaquette]

theorem adjacentEvenFixedSpatialLink_mem_lowerTemporalEdges
    (radius : Nat) :
    adjacentEvenFixedSpatialLink radius ∈
      edgesOf (adjacentEvenLowerTemporalPlaquette radius) := by
  unfold adjacentEvenFixedSpatialLink
    adjacentEvenLowerTemporalPlaquette edgesOf
  simp only [dirsOf, addE]
  exact List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)

theorem adjacentEvenFixedSpatialLink_mem_upperTemporalEdges
    (radius : Nat) :
    adjacentEvenFixedSpatialLink radius ∈
      edgesOf (adjacentEvenUpperTemporalPlaquette radius) := by
  unfold adjacentEvenFixedSpatialLink
    adjacentEvenUpperTemporalPlaquette edgesOf
  simp only [dirsOf, addE]
  exact List.mem_cons_self

/-- A fixed even-plane link reads both lower and upper face coordinates, so
the odd theorem `fixed_link_incident_face_fixed` has no even analogue. -/
theorem adjacentEven_fixedLink_incident_faces_not_fixed_only
    (radius : Nat) :
    (∃ lowerFace,
      adjacentEvenPlaquetteSide radius lowerFace = .lower ∧
      adjacentEvenFixedSpatialLink radius ∈ edgesOf lowerFace) ∧
    (∃ upperFace,
      adjacentEvenPlaquetteSide radius upperFace = .upper ∧
      adjacentEvenFixedSpatialLink radius ∈ edgesOf upperFace) := by
  exact ⟨
    ⟨adjacentEvenLowerTemporalPlaquette radius,
      adjacentEvenLowerTemporalPlaquette_side radius,
      adjacentEvenFixedSpatialLink_mem_lowerTemporalEdges radius⟩,
    ⟨adjacentEvenUpperTemporalPlaquette radius,
      adjacentEvenUpperTemporalPlaquette_side radius,
      adjacentEvenFixedSpatialLink_mem_upperTemporalEdges radius⟩⟩

#print axioms adjacentEvenPlaquetteSide_reflection
#print axioms adjacentEvenLinkSide_reflection
#print axioms adjacentEvenSlabFaceIdParts_perm
#print axioms adjacentEvenSlabLinkParts_perm
#print axioms adjacentEvenSlabFaceReflectId_side
#print axioms adjacentEvenSlabLink_reflection_side
#print axioms adjacentEvenFixedSpatialLink_side
#print axioms adjacentEvenFixedSpatialLink_mem_lowerTemporalEdges
#print axioms adjacentEvenFixedSpatialLink_mem_upperTemporalEdges
#print axioms adjacentEven_fixedLink_incident_faces_not_fixed_only

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
