/-
# Peel the two certified stretched-root components

Both positive root-face edges now belong to one finite global graph built from
the certified source presentation.  This file roots that graph at the two
edge sources, takes the Boolean union of their constructive components, and
pulls the resulting selection back to every displayed link.  Generic coherent
strand removal then supplies one common lowered physical field and a complete
accepted presented assignment over it.

The union is used without asserting that the two components are equal or
different.  Since it selects slot zero on each root face, the resulting
physical labelling decreases strictly at both faces.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Two constructive seeds in the completed graph -/

def certifiedStretchedLeftRootSeed
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    SlabFaceStrandSeed
      (CertifiedCubeSourcePresentedFaceStrandEdges stretched background) :=
  SlabFaceStrandSeed.ofEdge
    (certifiedStretchedLeftRootEdge_mem_complete stretched background)

def certifiedStretchedRightRootSeed
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    SlabFaceStrandSeed
      (CertifiedCubeSourcePresentedFaceStrandEdges stretched background) :=
  SlabFaceStrandSeed.ofEdge
    (certifiedStretchedRightRootEdge_mem_complete stretched background)

@[simp] theorem certifiedStretchedLeftRootSeed_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedLeftRootSeed stretched background).root =
      certifiedStretchedLeftRootCopy stretched :=
  certifiedStretchedLeftRootEdge_source stretched

@[simp] theorem certifiedStretchedRightRootSeed_root
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedRightRootSeed stretched background).root =
      certifiedStretchedRightRootCopy stretched :=
  certifiedStretchedRightRootEdge_source stretched

/-! ## 2. Union closure at every presented link -/

def certifiedStretchedComponentUnionSelected
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (copy : SlabFaceStrandCopy physical) : Bool :=
  (certifiedStretchedLeftRootSeed stretched background).selected copy ||
    (certifiedStretchedRightRootSeed stretched background).selected copy

theorem certifiedStretchedComponentUnionSelected_eq_of_edge_mem
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    {edge : SlabFaceStrandEdge physical}
    (hedge : edge ∈
      CertifiedCubeSourcePresentedFaceStrandEdges stretched background) :
    certifiedStretchedComponentUnionSelected stretched background edge.target =
      certifiedStretchedComponentUnionSelected stretched background edge.source := by
  unfold certifiedStretchedComponentUnionSelected
  rw [SlabFaceStrandSeed.selected_eq_of_edge_mem _ hedge,
    SlabFaceStrandSeed.selected_eq_of_edge_mem _ hedge]

/-- Package the common union once, together with its partner-closure proof at
every independently presented link. -/
def certifiedStretchedComponentUnionSelection
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PresentedSlabPartnerClosedFaceSelection K 1 physical
      (boundaryCompleteSlabLinks 1)
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background) :=
  PresentedSlabPartnerClosedFaceSelection.ofSeedUnion
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

/-- The two-root union is closed under the exact local partner at every link
of the completed certified presentation. -/
def certifiedStretchedComponentUnionAtLinkSelection
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    OrderedSlabLinkPartnerClosedFaceSelection K
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background linked) :=
  (certifiedStretchedComponentUnionSelection stretched background).atLink linked

@[simp] theorem certifiedStretchedComponentUnionSelected_leftRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionSelection
      stretched background).selected
      (certifiedStretchedLeftRootCopy stretched) = true := by
  rw [← certifiedStretchedLeftRootSeed_root stretched background]
  exact
    PresentedSlabPartnerClosedFaceSelection.ofSeedUnion_selected_leftRoot
      (certifiedStretchedLeftRootSeed stretched background)
      (certifiedStretchedRightRootSeed stretched background)

@[simp] theorem certifiedStretchedComponentUnionSelected_rightRoot
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionSelection
      stretched background).selected
      (certifiedStretchedRightRootCopy stretched) = true := by
  rw [← certifiedStretchedRightRootSeed_root stretched background]
  exact
    PresentedSlabPartnerClosedFaceSelection.ofSeedUnion_selected_rightRoot
      (certifiedStretchedLeftRootSeed stretched background)
      (certifiedStretchedRightRootSeed stretched background)

/-! ## 3. Compile the union to an accepted common physical peel -/

abbrev CertifiedStretchedComponentUnionLowerPhysical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) : EdgeLabelling :=
  (certifiedStretchedComponentUnionSelection stretched background).lowerPhysical

def certifiedStretchedComponentUnionLoweredWitnessAt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    PresentedSlabLinkFusionWitness K 1
      (CertifiedStretchedComponentUnionLowerPhysical stretched background)
      linked.1 :=
  (certifiedStretchedComponentUnionSelection
    stretched background).loweredWitnessAt linked

/-- Peeling the union at every link preserves a complete accepted presented
assignment over one common lowered physical field. -/
def certifiedStretchedComponentUnionLoweredAssignment
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PresentedSlabFusionWitnessAssignment K 1
      (CertifiedStretchedComponentUnionLowerPhysical stretched background)
      (boundaryCompleteSlabLinks 1) :=
  (certifiedStretchedComponentUnionSelection
    stretched background).loweredAssignment

/-- The accepted union peel strictly lowers the left root-face label. -/
theorem certifiedStretchedComponentUnionLowerPhysical_leftRoot_lt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    CertifiedStretchedComponentUnionLowerPhysical stretched background
        (certifiedStretchedLeftRootCopy stretched).faceId <
      physical (certifiedStretchedLeftRootCopy stretched).faceId := by
  apply
    (certifiedStretchedComponentUnionSelection
      stretched background).lowerPhysical_lt_of_selected
  exact certifiedStretchedComponentUnionSelected_leftRoot
    stretched background

/-- The same accepted peel strictly lowers the right root-face label. -/
theorem certifiedStretchedComponentUnionLowerPhysical_rightRoot_lt
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    CertifiedStretchedComponentUnionLowerPhysical stretched background
        (certifiedStretchedRightRootCopy stretched).faceId <
      physical (certifiedStretchedRightRootCopy stretched).faceId := by
  apply
    (certifiedStretchedComponentUnionSelection
      stretched background).lowerPhysical_lt_of_selected
  exact certifiedStretchedComponentUnionSelected_rightRoot
    stretched background

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.certifiedStretchedComponentUnionSelected_eq_of_edge_mem
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.certifiedStretchedComponentUnionAtLinkSelection
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.certifiedStretchedComponentUnionLoweredAssignment
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.certifiedStretchedComponentUnionLowerPhysical_leftRoot_lt
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel.certifiedStretchedComponentUnionLowerPhysical_rightRoot_lt
