/-
# The physical multiplicity code for the certified stretched-root union

This module instantiates the connected shape-to-physical compiler on the
actual certified first-stretched BF4 source.  One flat record supplies the
two-root presented animal, its exact physical peel budget, corrected-slab
support, and the selected strand-copy count.

The shape compiler first emits and decodes one `625 ^ peelSize` animal word.
The physical compiler then writes one multiplicity per plaquette in that
canonical decoded order and emits a binary word in a carrier of exact size
`4 ^ peelSize`.  Thus component overlap is counted once in both factors.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimalTourCode
import YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimalTourCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeakCompositionCode
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.RootedZ4AnimalPaddedTourCode
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. The one observable record passed through both compilers -/

/-- The actual certified union with its physical multiplicity function and
exact common peel budget. -/
def certifiedStretchedComponentUnionShapePhysicalData
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    SlabRootedAnimalMultiplicityData 1 where
  root := slabPlaquetteAt 1
    (certifiedStretchedLeftRootSeed stretched background).root.faceId
  support := presentedSeedUnionPlaquetteSupport
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
  root_mem := presentedLeftRootPlaquette_mem_seedUnionSupport
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
  support_nodup := presentedSeedUnionPlaquetteSupport_nodup
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
  connected := presentedSeedUnionPlaquetteSupport_connected
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
    (certifiedStretchedSeedRootPlaquettesAdjacent stretched background)
  budget := (certifiedStretchedComponentUnionSupportedSelection
    stretched background).peelFaces.length
  support_length_le_budget := presentedSeedUnionPlaquetteSupport_length_le_peelFaces
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
  support_boundary := by
    intro plaquette hplaquette
    have hraw := List.mem_eraseDups.mp hplaquette
    rcases List.mem_append.mp hraw with hleft | hright
    · exact presentedComponentPlaquetteSupport_subset_boundaryCompleteSlab
        (certifiedStretchedLeftRootSeed stretched background)
        plaquette hleft
    · exact presentedComponentPlaquetteSupport_subset_boundaryCompleteSlab
        (certifiedStretchedRightRootSeed stretched background)
        plaquette hright
  multiplicity := slabFaceStrandSelectionCount
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).closed.selected
  total_multiplicity_le_budget := Nat.le_of_eq
    (presentedSelection_peelFaces_length_eq_physicalDrop_l1
      (certifiedStretchedComponentUnionSupportedSelection
        stretched background)).symm

/-! ## 2. The connected shape and physical words -/

/-- The shape word emitted by the connected two-compiler record. -/
def certifiedStretchedComponentUnionConnectedShapeCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    List (Fin (z4Chain.D + 1)) :=
  slabRootedAnimalShapeCode
    (certifiedStretchedComponentUnionShapePhysicalData stretched background)

/-- The physical multiplicity word emitted after canonical shape decoding. -/
def certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) : List Nat :=
  slabRootedAnimalPhysicalMultiplicityBinaryCode
    (certifiedStretchedComponentUnionShapePhysicalData stretched background)

/-- The connected shape word lies in its exact common-budget carrier. -/
theorem certifiedStretchedComponentUnionConnectedShapeCode_mem_carrier
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedComponentUnionConnectedShapeCode stretched background ∈
      rootedZ4AnimalPaddedTourCarrier
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).budget :=
  slabRootedAnimalShapeCode_mem_carrier
    (certifiedStretchedComponentUnionShapePhysicalData stretched background)

/-- The connected physical word lies in a carrier of exact size
`4 ^ peelSize`. -/
theorem certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode_mem_carrier
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
        stretched background ∈
      allSeqs 2 (2 *
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).budget) :=
  slabRootedAnimalPhysicalMultiplicityBinaryCode_mem_carrier
    (certifiedStretchedComponentUnionShapePhysicalData stretched background)

/-- Decoding the physical word recovers every canonical support-ordered
multiplicity literally. -/
theorem certifiedStretchedComponentUnionPhysicalMultiplicityBinaryDecode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    weakCompositionBinaryDecode
        (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
          stretched background) =
      slabDecodedPhysicalMultiplicityWord
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).toDecodedPhysical :=
  slabRootedAnimalPhysicalMultiplicityBinaryDecode
    (certifiedStretchedComponentUnionShapePhysicalData stretched background)

/-- The common physical carrier has the exact `4 ^ peelSize` cardinality. -/
theorem certifiedStretchedComponentUnionPhysicalMultiplicityCarrier_length
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (allSeqs 2 (2 *
      (certifiedStretchedComponentUnionShapePhysicalData
        stretched background).budget)).length =
      4 ^ (certifiedStretchedComponentUnionShapePhysicalData
        stretched background).budget :=
  slabDecodedPhysicalMultiplicityCarrier_length _

#print axioms certifiedStretchedComponentUnionShapePhysicalData
#print axioms certifiedStretchedComponentUnionConnectedShapeCode
#print axioms certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
#print axioms certifiedStretchedComponentUnionConnectedShapeCode_mem_carrier
#print axioms certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode_mem_carrier
#print axioms certifiedStretchedComponentUnionPhysicalMultiplicityBinaryDecode
#print axioms certifiedStretchedComponentUnionPhysicalMultiplicityCarrier_length

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
