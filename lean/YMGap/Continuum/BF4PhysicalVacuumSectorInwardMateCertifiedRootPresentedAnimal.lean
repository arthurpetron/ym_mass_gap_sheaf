/-
# The certified first-stretched union is one rooted Z4 animal

The two roots retained by a certified first-stretched BF4 source are distinct
cube faces incident on the same literal slab link.  This file packages that
shared link as a genuine Z4 plaquette adjacency and specializes the generic
presented-component union theorem.

Consequently the complete two-root strand selection has one duplicate-free
connected physical support, rooted at the left certified face, whose size is
bounded by the exact physical peel mass.  No equality or disjointness decision
between the two strand components is needed.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
import YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimal

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowBound
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The two certified roots share their recorded physical link -/

/-- The recorded first-stretched cube link witnesses genuine adjacency of the
two certified root plaquettes. -/
def certifiedStretchedRootPlaquettesAdjacent
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt 1 (certifiedStretchedLeftRootCopy stretched).faceId)
      (slabPlaquetteAt 1 (certifiedStretchedRightRootCopy stretched).faceId) := by
  refine { link := stretched.root.1.1.link, on_p := ?_, on_q := ?_ }
  · change decide
      (stretched.root.1.1.link ∈ edgesOf
        (slabPlaquetteAt 1
          (certifiedStretchedLeftRootCopy stretched).faceId)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
        (cubeProductionIncidence_numeric_exact stretched.root.1.2).1)
  · change decide
      (stretched.root.1.1.link ∈ edgesOf
        (slabPlaquetteAt 1
          (certifiedStretchedRightRootCopy stretched).faceId)) = true
    exact decide_eq_true_eq.mpr
      (link_mem_edgesOf_slabPlaquetteAt_of_mem_incident
        (cubeProductionIncidence_numeric_exact stretched.root.1.2).2.1)

/-! ## 2. The actual certified union support -/

def certifiedStretchedComponentUnionPlaquetteSupport
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) : List Z4Plaq :=
  presentedSeedUnionPlaquetteSupport
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

theorem certifiedStretchedComponentUnionPlaquetteSupport_nodup
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionPlaquetteSupport
      stretched background).Nodup :=
  presentedSeedUnionPlaquetteSupport_nodup
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

theorem certifiedStretchedLeftRootPlaquette_mem_unionSupport
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    slabPlaquetteAt 1 (certifiedStretchedLeftRootCopy stretched).faceId ∈
      certifiedStretchedComponentUnionPlaquetteSupport
        stretched background := by
  unfold certifiedStretchedComponentUnionPlaquetteSupport
  rw [← certifiedStretchedLeftRootSeed_root stretched background]
  exact presentedLeftRootPlaquette_mem_seedUnionSupport
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

theorem certifiedStretchedRightRootPlaquette_mem_unionSupport
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    slabPlaquetteAt 1 (certifiedStretchedRightRootCopy stretched).faceId ∈
      certifiedStretchedComponentUnionPlaquetteSupport
        stretched background := by
  unfold certifiedStretchedComponentUnionPlaquetteSupport
  rw [← certifiedStretchedRightRootSeed_root stretched background]
  exact presentedRightRootPlaquette_mem_seedUnionSupport
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

/-- The actual first-stretched two-root union is one genuine connected Z4
lattice animal. -/
theorem certifiedStretchedComponentUnionPlaquetteAnimal
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    IsClusterThroughIn z4Chain
      (slabPlaquetteAt 1
        (certifiedStretchedLeftRootSeed stretched background).root.faceId)
      (presentedSeedUnionPlaquetteSupport
        (certifiedStretchedLeftRootSeed stretched background)
        (certifiedStretchedRightRootSeed stretched background)).length
      (presentedSeedUnionPlaquetteSupport
        (certifiedStretchedLeftRootSeed stretched background)
        (certifiedStretchedRightRootSeed stretched background)) := by
  have hadjacent : z4Chain.toLattice.Adjacent
      (slabPlaquetteAt 1
        (certifiedStretchedLeftRootSeed stretched background).root.faceId)
      (slabPlaquetteAt 1
        (certifiedStretchedRightRootSeed stretched background).root.faceId) := by
    rw [certifiedStretchedLeftRootSeed_root stretched background,
      certifiedStretchedRightRootSeed_root stretched background]
    exact certifiedStretchedRootPlaquettesAdjacent stretched
  exact presentedSeedUnionPlaquetteAnimal
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
    hadjacent

/-- The connected union support is paid once by the exact certified peel mass,
so component overlap never creates a second shape factor. -/
theorem certifiedStretchedComponentUnionPlaquetteSupport_length_le_peelFaces
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionPlaquetteSupport
        stretched background).length <=
      (certifiedStretchedComponentUnionSupportedSelection
        stretched background).peelFaces.length := by
  exact presentedSeedUnionPlaquetteSupport_length_le_peelFaces
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)

#print axioms certifiedStretchedRootPlaquettesAdjacent
#print axioms certifiedStretchedComponentUnionPlaquetteSupport
#print axioms certifiedStretchedComponentUnionPlaquetteAnimal
#print axioms certifiedStretchedComponentUnionPlaquetteSupport_length_le_peelFaces

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimal
