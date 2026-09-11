/-
# Exact full-source cardinality of the two classifier branches

The cube classifier partitions every root-first boundary source into either
an all-target assignment or a first-stretched source.  Both branches share the
same independent production assignment on the off-cube slab links.  This
module forms the missing all-target Cartesian carrier and proves that its
cardinality plus the existing first-stretched full-source cardinality is
exactly the complete extent-one SU(2) slab-link multiplicity.

This is a finite carrier identity only.  No weighted normalization, success
fraction, conditional transition estimate, or spectral claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceMultiplicitySplit

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceMultiplicitySplit
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. The complete all-target Cartesian branch -/

/-- One classified all-target cube assignment paired with one accepted
production assignment on exactly the off-cube links. -/
abbrev CubeInwardMateCertifiedTargetFullSource
    (K : Nat) (physical : EdgeLabelling) :=
  CubeInwardMateOrderedTargetWitnessAssignment K physical ×
    { assignment : SlabFusionWitnessAssignment //
      assignment ∈
        cubeInwardMateOffCubeFusionWitnessAssignments K physical }

/-- The literal all-target branch after restoring every off-cube production
coordinate. -/
def cubeInwardMateCertifiedTargetFullSources
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeInwardMateCertifiedTargetFullSource K physical) :=
  cartesian
    (cubeInwardMateCertifiedTargetAssignments
      K physical hK hbounded)
    (cubeInwardMateOffCubeFusionWitnessAssignments K physical).attach

private theorem cartesian_length_local {A B : Type}
    (left : List A) (right : List B) :
    (cartesian left right).length = left.length * right.length := by
  induction left with
  | nil =>
      unfold cartesian
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      rw [cartesian]
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      change right.length + (cartesian tail right).length =
        (tail.length + 1) * right.length
      rw [ih, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

/-- Restoring the off-cube coordinates multiplies the all-target branch size
by precisely the off-cube production multiplicity. -/
theorem cubeInwardMateCertifiedTargetFullSources_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetFullSources
      K physical hK hbounded).length =
      (cubeInwardMateCertifiedTargetAssignments
        K physical hK hbounded).length *
        natListProduct
          (slabExplicitLinkMultiplicity K 1 physical)
          cubeInwardMateOffCubeSlabLinks := by
  unfold cubeInwardMateCertifiedTargetFullSources
  rw [cartesian_length_local, List.length_attach,
    cubeInwardMateOffCubeFusionWitnessAssignments_length]

/-- No complete all-target branch entry is enumerated twice. -/
theorem cubeInwardMateCertifiedTargetFullSources_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetFullSources
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedTargetFullSources
  exact cartesian_nodup _ _
    (cubeInwardMateCertifiedTargetAssignments_nodup
      K physical hK hbounded)
    (attach_nodup_of_nodup _
      (cubeInwardMateOffCubeFusionWitnessAssignments_nodup
        K physical))

/-! ## 2. Exact full-slab branch conservation -/

/-- The completed all-target and first-stretched carriers partition the
entire extent-one source multiplicity. -/
theorem cubeInwardMateCertifiedFullSourceBranches_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetFullSources
        K physical hK hbounded).length +
      (cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded).length =
      slabExplicitLinkMultiplicityProduct K 1 physical := by
  rw [cubeInwardMateCertifiedTargetFullSources_length,
    cubeInwardMateCertifiedFirstStretchedFullSources_length]
  rw [← Nat.add_mul,
    cubeInwardMateCertifiedBranches_length K physical hK hbounded]
  exact cubeInwardMateSourceBoundary_mul_offCube_eq_slabMultiplicity
    K physical

/-- Attaching the existing first-stretched peel data loses no cardinality, so
the same exact conservation law holds for its downstream enumerated carrier. -/
theorem cubeInwardMateCertifiedTarget_add_enumeratedFirstStretched_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedTargetFullSources
        K physical hK hbounded).length +
      (enumeratedCubeInwardMateFullSources
        K physical hK hbounded).length =
      slabExplicitLinkMultiplicityProduct K 1 physical := by
  rw [enumeratedCubeInwardMateFullSources_length]
  exact cubeInwardMateCertifiedFullSourceBranches_length
    K physical hK hbounded

#print axioms cubeInwardMateCertifiedTargetFullSources_length
#print axioms cubeInwardMateCertifiedTargetFullSources_nodup
#print axioms cubeInwardMateCertifiedFullSourceBranches_length
#print axioms cubeInwardMateCertifiedTarget_add_enumeratedFirstStretched_length

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceBranchCardinality
