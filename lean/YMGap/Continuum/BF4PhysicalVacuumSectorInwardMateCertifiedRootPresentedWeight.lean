/-
# Exact weight payment for the certified stretched-root component union

The completed certified cube presentation contains two distinguished positive
root-face strand copies.  Their rooted component union is already known to be
partner closed.  This file adds physical support, serializes the union as one
legal repeated face peel, proves that the word contains at least the two
distinct root faces, reconstructs the physical source exactly, and applies the
cutoff-independent anchor heat payment to the actual presented source entry.

This is a pointwise source-to-target comparison.  It does not yet encode the
auxiliary inverse data or prove a multiplicity bound for all sources above one
target.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CompactDualSlabExpandedFacePeelWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The supported two-root selection -/

def certifiedStretchedComponentUnionSupportedSelection
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PresentedSlabSupportedPartnerClosedFaceSelection K 1 physical
      (boundaryCompleteSlabLinks 1)
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background) :=
  PresentedSlabSupportedPartnerClosedFaceSelection.ofSeedUnion
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

theorem certifiedStretchedRootFaceIds_ne
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    (certifiedStretchedLeftRootCopy stretched).faceId ≠
      (certifiedStretchedRightRootCopy stretched).faceId := by
  change centralLowerCubeFaceId stretched.root.1.1.left ≠
    centralLowerCubeFaceId stretched.root.1.1.right
  exact (cubeProductionIncidence_numeric_exact stretched.root.1.2).2.2.1

@[simp] theorem certifiedStretchedComponentUnionSupportedSelected_leftRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).closed.selected
      (certifiedStretchedLeftRootCopy stretched) = true := by
  exact certifiedStretchedComponentUnionSelected_leftRoot stretched background

@[simp] theorem certifiedStretchedComponentUnionSupportedSelected_rightRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).closed.selected
      (certifiedStretchedRightRootCopy stretched) = true := by
  exact certifiedStretchedComponentUnionSelected_rightRoot stretched background

/-! ## 2. Exact physical word and reconstruction -/

/-- The serialized union removes at least the two distinct certified root
faces. -/
theorem certifiedStretchedComponentUnion_two_le_peelFaces_length
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    2 ≤ (certifiedStretchedComponentUnionSupportedSelection
      stretched background).peelFaces.length := by
  apply
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).two_le_peelFaces_length_of_selected_faceId_ne
      (certifiedStretchedLeftRootCopy stretched)
      (certifiedStretchedRightRootCopy stretched)
  · exact certifiedStretchedComponentUnionSupportedSelected_leftRoot
      stretched background
  · exact certifiedStretchedComponentUnionSupportedSelected_rightRoot
      stretched background
  · exact certifiedStretchedRootFaceIds_ne stretched

def certifiedStretchedComponentUnionPeelPath
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    SlabFacePeelPath K 1 physical
      (certifiedStretchedComponentUnionSupportedSelection
        stretched background).peelFaces
      (CertifiedStretchedComponentUnionLowerPhysical
        stretched background) :=
  (certifiedStretchedComponentUnionSupportedSelection
    stretched background).peelPath hbounded

/-- The physical source is exactly recoverable from the lowered target and
the finite peel word. -/
theorem certifiedStretchedComponentUnion_reconstructPhysical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    raiseEdgeLabellingBy
        (CertifiedStretchedComponentUnionLowerPhysical stretched background)
        (fun faceId =>
          (certifiedStretchedComponentUnionSupportedSelection
            stretched background).peelFaces.count faceId) =
      physical :=
  (certifiedStretchedComponentUnionSupportedSelection
    stretched background).reconstructPhysical

/-! ## 3. Pointwise exact anchor payment -/

/-- The actual certified presented source pays one exact anchor coefficient
for every letter of its serialized component peel. -/
theorem certifiedStretchedComponentUnion_expandedFiberWeight_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    presentedSlabFusionWitnessAssignmentFiberWeight D physical
        (completePresentedSlabSourceOfCertifiedCube
          K physical hK hbounded stretched.certified background) <=
      anchorFaceCoefficient ^
          (certifiedStretchedComponentUnionSupportedSelection
            stretched background).peelFaces.length *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          (CertifiedStretchedComponentUnionLowerPhysical stretched background)
          (certifiedStretchedComponentUnionLoweredAssignment
            stretched background) := by
  dsimp only
  exact
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).expandedFiberWeight_le K 0 hbounded

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.certifiedStretchedRootFaceIds_ne
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.certifiedStretchedComponentUnion_two_le_peelFaces_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.certifiedStretchedComponentUnionPeelPath
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.certifiedStretchedComponentUnion_reconstructPhysical
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight.certifiedStretchedComponentUnion_expandedFiberWeight_le
