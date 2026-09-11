/-
# Global strand edges at the certified first-stretched cube root

The source classifier already retains an accepted root-first witness at every
cube incidence.  On its first-stretched branch, the debt certificate proves
that the first two displayed faces carry slot zero.  This file constructs
those two canonical physical terminals directly in the certified witness,
forgets their local addresses to global face-copy edges, and proves that both
edges occur in the completed presented slab graph.

This bypasses the older coarse carrier: no reconstruction of a separate
root word or channel history is needed.  The complete off-cube background
remains an explicit input.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
import YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabOrderedLinkGlobalFaceStrandEdge
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Literal positive root copies and their ordered positions -/

/-- Slot zero on the certified stretched root's left cube face. -/
def certifiedStretchedLeftRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) : SlabFaceStrandCopy physical where
  faceId := centralLowerCubeFaceId stretched.root.1.1.left
  slot := ⟨0, stretched.root.2.left_pos⟩

/-- Slot zero on the certified stretched root's right cube face. -/
def certifiedStretchedRightRootCopy
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) : SlabFaceStrandCopy physical where
  faceId := centralLowerCubeFaceId stretched.root.1.1.right
  slot := ⟨0, stretched.root.2.right_pos⟩

/-- The left root face occupies position zero in the certified source order. -/
def certifiedStretchedLeftRootPosition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    Fin (cubeInwardMateSourceFaceOrder stretched.root.1).faceIds.length :=
  ⟨0, by simp [cubeInwardMateSourceFaceOrder]⟩

/-- The right root face occupies position one in the certified source order. -/
def certifiedStretchedRightRootPosition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    Fin (cubeInwardMateSourceFaceOrder stretched.root.1).faceIds.length :=
  ⟨1, by simp [cubeInwardMateSourceFaceOrder]⟩

def certifiedStretchedLeftRootSlot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    Fin (physical ((cubeInwardMateSourceFaceOrder stretched.root.1).faceIds.get
      (certifiedStretchedLeftRootPosition stretched))) :=
  ⟨0, by
    simpa [certifiedStretchedLeftRootPosition,
      cubeInwardMateSourceFaceOrder] using stretched.root.2.left_pos⟩

def certifiedStretchedRightRootSlot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    Fin (physical ((cubeInwardMateSourceFaceOrder stretched.root.1).faceIds.get
      (certifiedStretchedRightRootPosition stretched))) :=
  ⟨0, by
    simpa [certifiedStretchedRightRootPosition,
      cubeInwardMateSourceFaceOrder] using stretched.root.2.right_pos⟩

/-! ## 2. The two certified root terminals and global edges -/

/-- The accepted root-first source witness already retained by certification. -/
def certifiedStretchedRootPresentedWitness
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    PresentedSlabLinkFusionWitness K 1 physical stretched.root.1.1.link :=
  cubeInwardMatePresentedSourceAssignmentOfCertified
    K physical hK hbounded stretched.certified stretched.root.1

def certifiedStretchedLeftRootTerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    let witness := certifiedStretchedRootPresentedWitness stretched
    OrderedSlabLinkPhysicalStrandTerminal
      K physical witness.order witness.auxiliary witness.auxiliary_mem :=
  orderedSlabLinkPhysicalTerminalAt K physical
    (certifiedStretchedRootPresentedWitness stretched).order
    (certifiedStretchedRootPresentedWitness stretched).auxiliary
    (certifiedStretchedRootPresentedWitness stretched).auxiliary_mem
    (certifiedStretchedLeftRootPosition stretched)
    (certifiedStretchedLeftRootSlot stretched)

def certifiedStretchedRightRootTerminal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    let witness := certifiedStretchedRootPresentedWitness stretched
    OrderedSlabLinkPhysicalStrandTerminal
      K physical witness.order witness.auxiliary witness.auxiliary_mem :=
  orderedSlabLinkPhysicalTerminalAt K physical
    (certifiedStretchedRootPresentedWitness stretched).order
    (certifiedStretchedRootPresentedWitness stretched).auxiliary
    (certifiedStretchedRootPresentedWitness stretched).auxiliary_mem
    (certifiedStretchedRightRootPosition stretched)
    (certifiedStretchedRightRootSlot stretched)

def certifiedStretchedLeftRootEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) : SlabFaceStrandEdge physical :=
  let witness := certifiedStretchedRootPresentedWitness stretched
  orderedSlabLinkFaceStrandEdgeOfTerminal K physical witness.order
    witness.auxiliary witness.auxiliary_mem
    (certifiedStretchedLeftRootTerminal stretched)

def certifiedStretchedRightRootEdge
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) : SlabFaceStrandEdge physical :=
  let witness := certifiedStretchedRootPresentedWitness stretched
  orderedSlabLinkFaceStrandEdgeOfTerminal K physical witness.order
    witness.auxiliary witness.auxiliary_mem
    (certifiedStretchedRightRootTerminal stretched)

theorem certifiedStretchedLeftRootEdge_source
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    (certifiedStretchedLeftRootEdge stretched).source =
      certifiedStretchedLeftRootCopy stretched := by
  calc
    (certifiedStretchedLeftRootEdge stretched).source =
        orderedSlabLinkPhysicalCopyAt
          (certifiedStretchedRootPresentedWitness stretched).order
          (certifiedStretchedLeftRootPosition stretched)
          (certifiedStretchedLeftRootSlot stretched) :=
      orderedSlabLinkPhysicalTerminalAtFaceStrandCopy K physical
        (certifiedStretchedRootPresentedWitness stretched).order
        (certifiedStretchedRootPresentedWitness stretched).auxiliary
        (certifiedStretchedRootPresentedWitness stretched).auxiliary_mem
        (certifiedStretchedLeftRootPosition stretched)
        (certifiedStretchedLeftRootSlot stretched)
    _ = certifiedStretchedLeftRootCopy stretched := by
      rfl

theorem certifiedStretchedRightRootEdge_source
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    (certifiedStretchedRightRootEdge stretched).source =
      certifiedStretchedRightRootCopy stretched := by
  calc
    (certifiedStretchedRightRootEdge stretched).source =
        orderedSlabLinkPhysicalCopyAt
          (certifiedStretchedRootPresentedWitness stretched).order
          (certifiedStretchedRightRootPosition stretched)
          (certifiedStretchedRightRootSlot stretched) :=
      orderedSlabLinkPhysicalTerminalAtFaceStrandCopy K physical
        (certifiedStretchedRootPresentedWitness stretched).order
        (certifiedStretchedRootPresentedWitness stretched).auxiliary
        (certifiedStretchedRootPresentedWitness stretched).auxiliary_mem
        (certifiedStretchedRightRootPosition stretched)
        (certifiedStretchedRightRootSlot stretched)
    _ = certifiedStretchedRightRootCopy stretched := by
      rfl

/-! ## 3. Membership in one completed presented graph -/

abbrev CertifiedCubeSourcePresentedFaceStrandEdges
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :=
  presentedSlabFusionWitnessAssignmentFaceStrandEdges
    K 1 physical (boundaryCompleteSlabLinks 1)
    (completePresentedSlabSourceOfCertifiedCube
      K physical hK hbounded stretched.certified background)

theorem certifiedStretchedLeftRootEdge_mem_complete
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedLeftRootEdge stretched ∈
      CertifiedCubeSourcePresentedFaceStrandEdges stretched background := by
  exact
    presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem_of_eq
      K 1 physical (boundaryCompleteSlabLinks 1)
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background)
      (cubeProductionIncidenceSlabLink stretched.root.1)
      (certifiedStretchedRootPresentedWitness stretched)
      (completePresentedSlabSourceOfCertifiedCube_at_cube
        K physical hK hbounded stretched.certified background
        stretched.root.1)
      (certifiedStretchedLeftRootTerminal stretched)

theorem certifiedStretchedRightRootEdge_mem_complete
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedRightRootEdge stretched ∈
      CertifiedCubeSourcePresentedFaceStrandEdges stretched background := by
  exact
    presentedSlabFusionWitnessAssignmentFaceStrandEdgeOfTerminal_mem_of_eq
      K 1 physical (boundaryCompleteSlabLinks 1)
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background)
      (cubeProductionIncidenceSlabLink stretched.root.1)
      (certifiedStretchedRootPresentedWitness stretched)
      (completePresentedSlabSourceOfCertifiedCube_at_cube
        K physical hK hbounded stretched.certified background
        stretched.root.1)
      (certifiedStretchedRightRootTerminal stretched)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.certifiedStretchedLeftRootEdge_source
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.certifiedStretchedRightRootEdge_source
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.certifiedStretchedLeftRootEdge_mem_complete
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges.certifiedStretchedRightRootEdge_mem_complete
