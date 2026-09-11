/-
# Enumerate complete first-stretched slab sources without redundancy

The cube classifier now supplies a duplicate-free list of certified
first-stretched sources, and the off-cube completion layer supplies a
duplicate-free list of production assignments on exactly the complement of
the twelve cube links.  Their literal Cartesian product is therefore the
finite family of complete source data that survives the completion map.

This file constructs that product, proves its exact cardinality and
duplicate-freeness, and compiles every member to the complete presented and
raw source interfaces consumed by the certified two-root peel.  Injectivity
of the presented/raw compiler is the next theorem; no such claim is made
here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Exact Cartesian family -/

/-- One certified first-stretched cube source paired with one accepted
production assignment on exactly the off-cube links. -/
abbrev CubeInwardMateCertifiedFirstStretchedFullSource
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :=
  CubeInwardMateCertifiedFirstStretchedSource K physical hK hbounded ×
    { assignment : SlabFusionWitnessAssignment //
      assignment ∈
        cubeInwardMateOffCubeFusionWitnessAssignments K physical }

/-- The complete finite family with no discarded cube-background
coordinates. -/
def cubeInwardMateCertifiedFirstStretchedFullSources
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded) :=
  cartesian
    (cubeInwardMateCertifiedFirstStretchedSources
      K physical hK hbounded)
    (cubeInwardMateOffCubeFusionWitnessAssignments K physical).attach

private theorem cartesian_length {A B : Type}
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

/-- The full-source family has exactly cube first-stretched multiplicity times
the production multiplicity on the surviving off-cube links. -/
theorem cubeInwardMateCertifiedFirstStretchedFullSources_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedFirstStretchedFullSources
      K physical hK hbounded).length =
      (cubeInwardMateCertifiedFirstStretchedSources
        K physical hK hbounded).length *
        natListProduct
          (slabExplicitLinkMultiplicity K 1 physical)
          cubeInwardMateOffCubeSlabLinks := by
  unfold cubeInwardMateCertifiedFirstStretchedFullSources
  rw [cartesian_length, List.length_attach,
    cubeInwardMateOffCubeFusionWitnessAssignments_length]

/-- No complete source data pair is enumerated twice. -/
theorem cubeInwardMateCertifiedFirstStretchedFullSources_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedFirstStretchedFullSources
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedFirstStretchedFullSources
  exact cartesian_nodup _ _
    (cubeInwardMateCertifiedFirstStretchedSources_nodup
      K physical hK hbounded)
    (attach_nodup_of_nodup _
      (cubeInwardMateOffCubeFusionWitnessAssignments_nodup
        K physical))

/-- Membership retains both factors as explicit evidence. -/
theorem mem_cubeInwardMateCertifiedFirstStretchedFullSources_iff
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded) :
    source ∈ cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded ↔
      source.1 ∈ cubeInwardMateCertifiedFirstStretchedSources
          K physical hK hbounded ∧
        source.2 ∈
          (cubeInwardMateOffCubeFusionWitnessAssignments
            K physical).attach := by
  exact mem_cartesian_iff _ _ source

/-! ## 2. Compile a member to the downstream source interfaces -/

/-- The canonical complete presented source represented by one Cartesian
member. -/
def CubeInwardMateCertifiedFirstStretchedFullSource.toPresented
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded) :
    PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1) :=
  completePresentedSlabSourceOfFirstStretchedAndOffAssignment
    K physical hK hbounded source.1 source.2.1 source.2.2

/-- Forget only presentation orders and proofs, retaining the literal raw
auxiliary payload used by the expanded-fiber weight and inverse compiler. -/
def CubeInwardMateCertifiedFirstStretchedFullSource.toRaw
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded) : SlabFusionWitnessAssignment :=
  presentedSlabFusionWitnessAssignmentRaw
    (boundaryCompleteSlabLinks 1) source.toPresented

#print axioms cubeInwardMateCertifiedFirstStretchedFullSources_length
#print axioms cubeInwardMateCertifiedFirstStretchedFullSources_nodup
#print axioms mem_cubeInwardMateCertifiedFirstStretchedFullSources_iff
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toPresented
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toRaw

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
