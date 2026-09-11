/-
# The dependent twelve-link source-witness partition

The physical-link classifier is now applied simultaneously at every member of
the attached twelve-entry cube-incidence list.  The source carrier is a genuine
dependent product: each coordinate is accepted in its own literal root-first
face order.  The output retains the corresponding dependent `mate + debt`
choice at every coordinate.

Recovery is pointwise, so equality of two complete classified assignments
forces equality of their complete source assignments.  The original source
tuple also packages directly as a common family of accepted presented link
witnesses.  No anonymous natural-number product or pointwise permutation of
basis witnesses is used.

This file does not yet split the classified product into its all-target and
first-stretched branches, extend the cube family to the off-cube slab links,
or attach a peel/weight certificate to the stretched branch.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Dependent source and classified assignments -/

/-- One accepted root-first source witness at each of the twelve literal
cube-boundary incidences. -/
abbrev CubeInwardMateOrderedSourceWitnessAssignment
    (K : Nat) (physical : EdgeLabelling) :=
  (linked : CubeProductionIncidenceMember) →
    CubeInwardMateOrderedSourceWitness K physical linked

/-- The pointwise target-or-stretched output family, retaining the dependent
local fiber at each literal incidence. -/
abbrev CubeInwardMateClassifiedWitnessAssignment
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :=
  (linked : CubeProductionIncidenceMember) →
    Sum
      (CubeInwardMateOrderedTargetWitness K physical linked)
      (CubeInwardMateStretchedWitnessDebt
        K physical hK hbounded linked)

/-- Apply the literal-link source partition at all twelve dependent
coordinates. -/
def cubeInwardMateSourceAssignmentPartition
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded :=
  fun linked => cubeInwardMateSourceWitnessPartition
    K physical hK hbounded linked (source linked)

/-- Recover the complete source auxiliary family coordinate by coordinate.
Only the auxiliary values are needed for the global injectivity argument. -/
def recoverCubeInwardMateSourceAssignmentPartitionAt
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (classified : CubeInwardMateClassifiedWitnessAssignment
      K physical hK hbounded) :
    CubeProductionIncidenceMember → EdgeLabelling :=
  fun linked => recoverCubeInwardMateSourceWitnessPartitionAt
    K physical hK hbounded linked (classified linked)

theorem recoverCubeInwardMateSourceAssignmentPartitionAt_apply
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical)
    (linked : CubeProductionIncidenceMember) :
    recoverCubeInwardMateSourceAssignmentPartitionAt
        K physical hK hbounded
        (cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded source) linked =
      (source linked).1 :=
  recoverCubeInwardMateSourceWitnessPartitionAt_apply
    K physical hK hbounded linked (source linked)

/-- **Twelve-link multiplicity faithfulness.**  The dependent product of the
local physical-link classifiers is injective. -/
theorem cubeInwardMateSourceAssignmentPartition_injective
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    Function.Injective
      (cubeInwardMateSourceAssignmentPartition
        K physical hK hbounded) := by
  intro source₁ source₂ heq
  funext linked
  exact cubeInwardMateSourceWitnessPartition_injective
    K physical hK hbounded linked
    (congrFun heq linked)

/-! ## 2. The complete source tuple is already a presented cube family -/

/-- A common family of literal presented witnesses, indexed by the same
twelve incidences as the source product. -/
abbrev CubeInwardMatePresentedSourceAssignment
    (K : Nat) (physical : EdgeLabelling) :=
  (linked : CubeProductionIncidenceMember) →
    PresentedSlabLinkFusionWitness K 1 physical linked.1.link

/-- Package every source coordinate with the face order in which it was
proved accepted. -/
def cubeInwardMatePresentedSourceAssignment
    (K : Nat) (physical : EdgeLabelling)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical) :
    CubeInwardMatePresentedSourceAssignment K physical :=
  fun linked =>
    { order := cubeInwardMateSourceFaceOrder linked
      auxiliary := (source linked).1
      auxiliary_mem := (source linked).2 }

@[simp] theorem cubeInwardMatePresentedSourceAssignment_order
    (K : Nat) (physical : EdgeLabelling)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMatePresentedSourceAssignment
      K physical source linked).order =
      cubeInwardMateSourceFaceOrder linked :=
  rfl

@[simp] theorem cubeInwardMatePresentedSourceAssignment_auxiliary
    (K : Nat) (physical : EdgeLabelling)
    (source : CubeInwardMateOrderedSourceWitnessAssignment K physical)
    (linked : CubeProductionIncidenceMember) :
    (cubeInwardMatePresentedSourceAssignment
      K physical source linked).auxiliary =
      (source linked).1 :=
  rfl

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.cubeInwardMateSourceAssignmentPartition
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.recoverCubeInwardMateSourceAssignmentPartitionAt_apply
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.cubeInwardMateSourceAssignmentPartition_injective
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition.cubeInwardMatePresentedSourceAssignment
