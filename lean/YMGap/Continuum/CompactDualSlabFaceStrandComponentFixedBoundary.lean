/-
# Exact fixed-time boundary criterion for a strand-component peel

The conditional-variance law groups half-states by one fixed-time boundary
channel.  A whole-slab strand-component peel is therefore useful for that
law only when it stays inside the same boundary fiber.

This file gives the exact criterion.  At every face, the lowered physical
label agrees with the source label if and only if the selected component has
zero strand multiplicity there.  Consequently a component peel preserves the
entire OS fixed-time boundary precisely when its selected multiplicity
vanishes on `centralFixedFaceIds`.

This is a boundary-preservation compiler, not a posterior-variance estimate:
it does not assert that every component avoids the interface, nor that the
interface-preserving components carry a uniform fraction of variance.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
import YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Exact pointwise preservation -/

/-- A component peel leaves one face label unchanged exactly when the
component selects no strand copy at that face. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerPhysical_eq_iff_selectionCount_zero
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faceId : Nat) :
    SlabFusionWitnessFaceStrandSeed.lowerPhysical seed faceId =
        physical faceId ↔
      slabFaceStrandSelectionCount seed.selected faceId = 0 := by
  have hcapacity :
      slabFaceStrandSelectionCount seed.selected faceId ≤ physical faceId :=
    slabFaceStrandSelectionCount_le seed.selected faceId
  unfold SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection lowerEdgeLabellingBy
  constructor
  · intro heq
    omega
  · intro hzero
    rw [hzero]
    exact Nat.sub_zero _

/-! ## 2. Preservation on an arbitrary face list -/

/-- The component has zero selected physical multiplicity on a displayed
face list. -/
def componentAvoidsFaces
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faces : List Nat) : Prop :=
  ∀ faceId, faceId ∈ faces →
    slabFaceStrandSelectionCount seed.selected faceId = 0

/-- Avoiding a face list is exactly agreement of source and lowered physical
labels on that list. -/
theorem componentAvoidsFaces_iff_lowerPhysical_agrees
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (faces : List Nat) :
    componentAvoidsFaces seed faces ↔
      ∀ faceId, faceId ∈ faces →
        SlabFusionWitnessFaceStrandSeed.lowerPhysical seed faceId =
          physical faceId := by
  constructor
  · intro havoid faceId hface
    exact
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical_eq_iff_selectionCount_zero
        seed faceId).mpr (havoid faceId hface)
  · intro hagree faceId hface
    exact
      (SlabFusionWitnessFaceStrandSeed.lowerPhysical_eq_iff_selectionCount_zero
        seed faceId).mp (hagree faceId hface)

/-! ## 3. The physical OS fixed-time boundary -/

/-- The exact condition that a component peel stay inside one fixed-time
boundary channel of the central reflected slab. -/
def componentPreservesCentralBoundary
    {K half : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn
        K (centralExtent half) physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K (centralExtent half) physical links assignment hassignment) : Prop :=
  componentAvoidsFaces seed (centralFixedFaceIds half)

/-- A component preserves the central OS boundary if and only if lowering it
leaves every literal fixed-time face coordinate unchanged. -/
theorem componentPreservesCentralBoundary_iff
    {K half : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn
        K (centralExtent half) physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K (centralExtent half) physical links assignment hassignment) :
    componentPreservesCentralBoundary seed ↔
      ∀ faceId, faceId ∈ centralFixedFaceIds half →
        SlabFusionWitnessFaceStrandSeed.lowerPhysical seed faceId =
          physical faceId := by
  exact componentAvoidsFaces_iff_lowerPhysical_agrees
    seed (centralFixedFaceIds half)

end YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary.SlabFusionWitnessFaceStrandSeed.lowerPhysical_eq_iff_selectionCount_zero
#print axioms
  YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary.componentAvoidsFaces_iff_lowerPhysical_agrees
#print axioms
  YMGap.Continuum.CompactDualSlabFaceStrandComponentFixedBoundary.componentPreservesCentralBoundary_iff
