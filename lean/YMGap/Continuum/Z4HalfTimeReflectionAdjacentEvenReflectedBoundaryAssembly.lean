/-
# Reflected half-state assembly on the adjacent-even slab

The palindromic sandwich must use one common finite half-state coordinate on
both sides.  This file supplies the missing adjacent-even analogue of the
older odd-slab assembly: a lower labelling, a fixed-plane labelling, and a
second lower labelling are assembled by reflection into one full physical
labelling.  Reflection swaps the two lower inputs and leaves the fixed input
unchanged, exactly and constructively.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPalindromicSandwich
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPartition

/-! ## 1. Literal adjacent-even face-coordinate lists -/

def adjacentEvenLowerFaceIds (radius : Nat) : List Nat :=
  (adjacentEvenSlabFaceIdParts radius).1

def adjacentEvenUpperFaceIds (radius : Nat) : List Nat :=
  (adjacentEvenSlabFaceIdParts radius).2.2

theorem mem_adjacentEvenLowerFaceIds {radius id : Nat} :
    id ∈ adjacentEvenLowerFaceIds radius ↔
      id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower := by
  exact mem_partitionBySide_lower _ _ _

theorem mem_adjacentEvenUpperFaceIds {radius id : Nat} :
    id ∈ adjacentEvenUpperFaceIds radius ↔
      id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) ∧
      adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id) = .upper := by
  exact mem_partitionBySide_upper _ _ _

/-! ## 2. Full labelling assembled from two common lower coordinates -/

def assembleAdjacentEvenReflectedSlabLabelling
    (radius : Nat) (left boundary right : EdgeLabelling) : EdgeLabelling :=
  fun id =>
    if id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius) then
      match adjacentEvenPlaquetteSide radius
          (slabPlaquetteAt (adjacentEvenExtent radius) id) with
      | .lower => left id
      | .fixed => boundary id
      | .upper => right
          (slabFaceReflectId (adjacentEvenExtent radius) id)
    else 0

theorem assembleAdjacentEvenReflectedSlabLabelling_lower
    {radius id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hside : adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id) = .lower) :
    assembleAdjacentEvenReflectedSlabLabelling
      radius left boundary right id = left id := by
  simp [assembleAdjacentEvenReflectedSlabLabelling, hid, hside]

theorem assembleAdjacentEvenReflectedSlabLabelling_fixed
    {radius id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hside : adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed) :
    assembleAdjacentEvenReflectedSlabLabelling
      radius left boundary right id = boundary id := by
  simp [assembleAdjacentEvenReflectedSlabLabelling, hid, hside]

theorem assembleAdjacentEvenReflectedSlabLabelling_upper
    {radius id : Nat} {left boundary right : EdgeLabelling}
    (hid : id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hside : adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id) = .upper) :
    assembleAdjacentEvenReflectedSlabLabelling
        radius left boundary right id =
      right (slabFaceReflectId (adjacentEvenExtent radius) id) := by
  simp [assembleAdjacentEvenReflectedSlabLabelling, hid, hside]

theorem assembleAdjacentEvenReflectedSlabLabelling_zero_off_physical
    (radius : Nat) (left boundary right : EdgeLabelling)
    {id : Nat}
    (hid : id ∉ slabPhysicalFaceEdges (adjacentEvenExtent radius)) :
    assembleAdjacentEvenReflectedSlabLabelling
      radius left boundary right id = 0 := by
  simp [assembleAdjacentEvenReflectedSlabLabelling, hid]

/-- Every enumerated adjacent-even assembly is a genuinely bounded production
face labelling. -/
theorem assembleAdjacentEvenReflectedSlabLabelling_bounded
    {K radius : Nat} {left boundary right : EdgeLabelling}
    (hleft : left ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius))
    (hboundary : boundary ∈ boundedEdgeLabellings K
      (adjacentEvenFixedFaceIds radius))
    (hright : right ∈ boundedEdgeLabellings K
      (adjacentEvenLowerFaceIds radius)) :
    SlabFaceLabellingBounded K (adjacentEvenExtent radius)
      (assembleAdjacentEvenReflectedSlabLabelling
        radius left boundary right) := by
  have hleftSound := boundedEdgeLabellings_sound K
    (adjacentEvenLowerFaceIds radius) left hleft
  have hboundarySound := boundedEdgeLabellings_sound K
    (adjacentEvenFixedFaceIds radius) boundary hboundary
  have hrightSound := boundedEdgeLabellings_sound K
    (adjacentEvenLowerFaceIds radius) right hright
  intro id hid
  cases hside : adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id)
  · rw [assembleAdjacentEvenReflectedSlabLabelling_lower hid hside]
    exact Nat.le_of_lt_succ
      (hleftSound.1 id
        (mem_adjacentEvenLowerFaceIds.mpr ⟨hid, hside⟩))
  · rw [assembleAdjacentEvenReflectedSlabLabelling_fixed hid hside]
    exact Nat.le_of_lt_succ
      (hboundarySound.1 id
        (mem_adjacentEvenFixedFaceIds.mpr ⟨hid, hside⟩))
  · rw [assembleAdjacentEvenReflectedSlabLabelling_upper hid hside]
    have hreflectedPhysical := slabFaceReflectId_physical hid
    have hreflectedSide := adjacentEvenSlabFaceReflectId_side hid
    rw [hside] at hreflectedSide
    exact Nat.le_of_lt_succ
      (hrightSound.1 _
        (mem_adjacentEvenLowerFaceIds.mpr
          ⟨hreflectedPhysical,
            by simpa [flipSide] using hreflectedSide⟩))

/-! ## 3. Exact reflection swap -/

theorem adjacentEvenTimeReflectPlaquette_eq_self_of_fixed_side
    {radius : Nat} {plaquette : Z4Plaq}
    (hside : adjacentEvenPlaquetteSide radius plaquette = .fixed) :
    timeReflectPlaquette (adjacentEvenExtent radius) plaquette =
      plaquette := by
  obtain ⟨⟨a, b, c, time⟩, plane⟩ := plaquette
  cases plane
  all_goals simp only [adjacentEvenPlaquetteSide] at hside
  all_goals simp only [timeReflectPlaquette, adjacentEvenExtent,
    centralExtent]
  all_goals
    simp only [adjacentEvenSpatialSide,
      adjacentEvenTemporalSide, adjacentEvenCenter] at hside
    repeat' split at hside
    all_goals simp_all
    all_goals omega

theorem adjacentEvenSlabFaceReflectId_eq_self_of_fixed_side
    {radius id : Nat}
    (hid : id ∈ slabPhysicalFaceEdges (adjacentEvenExtent radius))
    (hside : adjacentEvenPlaquetteSide radius
      (slabPlaquetteAt (adjacentEvenExtent radius) id) = .fixed) :
    slabFaceReflectId (adjacentEvenExtent radius) id = id := by
  apply slabPlaquetteAt_injective_on_physical
    (slabFaceReflectId_physical hid) hid
  rw [slabPlaquetteAt_slabFaceReflectId hid,
    adjacentEvenTimeReflectPlaquette_eq_self_of_fixed_side hside]

/-- Reflection exchanges the two lower-half inputs while retaining the same
fixed-plane input.  This is the literal common-coordinate identity required
by a palindromic `A T A^t` contraction. -/
theorem assembleAdjacentEvenReflectedSlabLabelling_reflection_swap
    (radius : Nat) (left boundary right : EdgeLabelling) :
    reflectSupportedSlabFaceLabelling (adjacentEvenExtent radius)
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) =
      assembleAdjacentEvenReflectedSlabLabelling
        radius right boundary left := by
  funext id
  by_cases hid : id ∈
      slabPhysicalFaceEdges (adjacentEvenExtent radius)
  · have hreflectedPhysical := slabFaceReflectId_physical hid
    have hreflectedSide := adjacentEvenSlabFaceReflectId_side hid
    cases hside : adjacentEvenPlaquetteSide radius
        (slabPlaquetteAt (adjacentEvenExtent radius) id)
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right
            (slabFaceReflectId (adjacentEvenExtent radius) id) =
        assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left id
      rw [assembleAdjacentEvenReflectedSlabLabelling_upper
          hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleAdjacentEvenReflectedSlabLabelling_lower hid hside,
        slabFaceReflectId_involutive hid]
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right
            (slabFaceReflectId (adjacentEvenExtent radius) id) =
        assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left id
      rw [assembleAdjacentEvenReflectedSlabLabelling_fixed
          hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleAdjacentEvenReflectedSlabLabelling_fixed hid hside,
        adjacentEvenSlabFaceReflectId_eq_self_of_fixed_side hid hside]
    · rw [hside] at hreflectedSide
      rw [reflectSupportedSlabFaceLabelling_eq_on_physical _ _ hid]
      change assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right
            (slabFaceReflectId (adjacentEvenExtent radius) id) =
        assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left id
      rw [assembleAdjacentEvenReflectedSlabLabelling_lower
          hreflectedPhysical
          (by simpa [flipSide] using hreflectedSide),
        assembleAdjacentEvenReflectedSlabLabelling_upper hid hside]
  · rw [reflectSupportedSlabFaceLabelling_zero_off_physical _ _ hid,
      assembleAdjacentEvenReflectedSlabLabelling_zero_off_physical
        radius right boundary left hid]

#print axioms assembleAdjacentEvenReflectedSlabLabelling_bounded
#print axioms adjacentEvenTimeReflectPlaquette_eq_self_of_fixed_side
#print axioms adjacentEvenSlabFaceReflectId_eq_self_of_fixed_side
#print axioms assembleAdjacentEvenReflectedSlabLabelling_reflection_swap

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
