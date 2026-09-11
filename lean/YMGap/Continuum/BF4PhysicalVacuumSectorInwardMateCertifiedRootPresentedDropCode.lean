/-
# A finite left-inverse code for the certified stretched-root peel

This file specializes the presented component drop code to the actual first
stretched source branch.  From the lowered accepted presented target and one
finite code, the decoder recovers both the literal source physical labelling
and every raw auxiliary payload used by the expanded-fiber weight.  The code's
physical word has length at least two and each link-local auxiliary word has
width at most three.  Certified face orders are retained by the target and
therefore cost no additional inverse-code coordinate.

This is exact reconstruction, not yet a bound on the number of possible
sparse codes above one target.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-- The finite physical-plus-auxiliary drop code of the certified two-root
component union. -/
def certifiedStretchedComponentUnionDropCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    SlabFaceStrandComponentDropCode :=
  presentedSlabSupportedSelectionDropCode
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background)

/-- Its physical word contains at least the two distinct certified root
faces. -/
theorem certifiedStretchedComponentUnionDropCode_two_le_physicalFaces_length
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    2 ≤ (certifiedStretchedComponentUnionDropCode
      stretched background).physicalFaces.length := by
  exact certifiedStretchedComponentUnion_two_le_peelFaces_length
    stretched background

/-- Every link-local auxiliary word has cutoff-independent width at most
three. -/
theorem certifiedStretchedComponentUnionAuxiliaryDropWord_length_le_three
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1))
    (link : SlabLink) :
    (presentedSlabSupportedSelectionAuxiliaryDropWordAt
      (certifiedStretchedComponentUnionSupportedSelection
        stretched background) link).length ≤ 3 :=
  presentedSlabSupportedSelectionAuxiliaryDropWordAt_length_le_three
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background) link

/-- The lowered accepted target and finite code recover the exact source pair
used by the expanded-fiber weight. -/
theorem certifiedStretchedComponentUnionDropCode_reconstructPresentedEntry
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    reconstructPresentedEntry
        (certifiedStretchedComponentUnionDropCode stretched background)
        (boundaryCompleteSlabLinks 1)
        (certifiedStretchedComponentUnionLoweredAssignment
          stretched background) =
      (physical,
        presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1)
          (completePresentedSlabSourceOfCertifiedCube
            K physical hK hbounded stretched.certified background)) :=
  presentedSlabSupportedSelectionDropCode_reconstructPresentedEntry
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background)

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.certifiedStretchedComponentUnionDropCode
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.certifiedStretchedComponentUnionDropCode_two_le_physicalFaces_length
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.certifiedStretchedComponentUnionAuxiliaryDropWord_length_le_three
#print axioms
  YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedDropCode.certifiedStretchedComponentUnionDropCode_reconstructPresentedEntry
