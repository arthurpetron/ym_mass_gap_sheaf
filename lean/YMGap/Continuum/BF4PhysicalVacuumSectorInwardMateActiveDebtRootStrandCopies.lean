/-
# Literal physical strand copies at an active inward-mate debt root

Every rooted active-debt carrier already proves that its two incident cube
faces have positive physical labels.  This file turns those two propositions
into the actual slot-zero `SlabFaceStrandCopy` values required by the global
strand graph.  It also retains their exact root-link incidence and proves that
the copies are distinct.

This is the last purely geometric seed step before the root auxiliary is
unfolded from its collapsed stretched-spin network into a source network.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or trusted external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
import YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootWitness
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateStretchedDebtRoot
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex

/-! ## 1. The two Type-level root copies -/

/-- Slot zero on the left incident positive face of the active root. -/
def leftRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : SlabFaceStrandCopy physical where
  faceId := centralLowerCubeFaceId
    (cubeDebtRootIncidence carrier.word).1.left
  slot := ⟨0, carrier.root_faces_positive.1⟩

/-- Slot zero on the right incident positive face of the active root. -/
def rightRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) : SlabFaceStrandCopy physical where
  faceId := centralLowerCubeFaceId
    (cubeDebtRootIncidence carrier.word).1.right
  slot := ⟨0, carrier.root_faces_positive.2⟩

@[simp] theorem leftRootCopy_faceId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (leftRootCopy carrier).faceId = centralLowerCubeFaceId
      (cubeDebtRootIncidence carrier.word).1.left := rfl

@[simp] theorem rightRootCopy_faceId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rightRootCopy carrier).faceId = centralLowerCubeFaceId
      (cubeDebtRootIncidence carrier.word).1.right := rfl

@[simp] theorem leftRootCopy_slot_val
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (leftRootCopy carrier).slot.val = 0 := rfl

@[simp] theorem rightRootCopy_slot_val
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rightRootCopy carrier).slot.val = 0 := rfl

/-! ## 2. Exact geometric incidence and separation -/

theorem leftRootCopy_mem_incident
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (leftRootCopy carrier).faceId ∈ slabIncidentPlaqIds 1
      (cubeDebtRootIncidence carrier.word).1.link := by
  exact (cubeProductionIncidence_numeric_exact
    (cubeDebtRootIncidence carrier.word).2).1

theorem rightRootCopy_mem_incident
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    (rightRootCopy carrier).faceId ∈ slabIncidentPlaqIds 1
      (cubeDebtRootIncidence carrier.word).1.link := by
  exact (cubeProductionIncidence_numeric_exact
    (cubeDebtRootIncidence carrier.word).2).2.1

/-- The two positive root strands are genuinely different face-copy
vertices, even though both use slot zero. -/
theorem leftRootCopy_ne_rightRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (carrier : CubeRootedActiveDebtFusionCarrier
      K physical hK hbounded) :
    leftRootCopy carrier ≠ rightRootCopy carrier := by
  intro heq
  have hface := congrArg SlabFaceStrandCopy.faceId heq
  exact (cubeProductionIncidence_numeric_exact
    (cubeDebtRootIncidence carrier.word).2).2.2.1 hface

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.leftRootCopy
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.rightRootCopy
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.leftRootCopy_mem_incident
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateActiveDebtRootStrandCopies.leftRootCopy_ne_rightRootCopy
