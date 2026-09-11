/-
# One padded shape code for the certified stretched-root union

The certified first-stretched BF4 source has two presented strand roots whose
plaquette supports form one connected, deduplicated Z4 animal.  This module
feeds that actual union into the reusable rooted-animal compiler.  The result
is one deterministic padded tour, not a pair of independent component codes.

If `peelSize` is the exact physical peel mass, the word belongs to a carrier
of exactly `625 ^ peelSize` elements and decodes back to the whole union
support.  Component overlap is therefore counted once and requires no
equality/disjointness case split.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimal
import YMGap.Continuum.RootedZ4AnimalPaddedTourCode

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimalTourCode

set_option autoImplicit false

open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootGlobalEdges
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimal
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAnimal
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.DecodeComplete
open YMGap.Continuum.RootedZ4AnimalPaddedTourCode
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Package the actual union as compiler data -/

/-- The two roots in the seed presentation retain the certified geometric
plaquette adjacency. -/
def certifiedStretchedSeedRootPlaquettesAdjacent
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    z4Chain.toLattice.Adjacent
      (slabPlaquetteAt 1
        (certifiedStretchedLeftRootSeed stretched background).root.faceId)
      (slabPlaquetteAt 1
        (certifiedStretchedRightRootSeed stretched background).root.faceId) := by
  rw [certifiedStretchedLeftRootSeed_root stretched background,
    certifiedStretchedRightRootSeed_root stretched background]
  exact certifiedStretchedRootPlaquettesAdjacent stretched

/-- The named certified union support retains the Type-valued internal
connectivity used by the generic compiler. -/
def certifiedStretchedComponentUnionPlaquetteSupport_connected
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    PolymerModel.connectedIn (L := z4Chain.toLattice)
      (certifiedStretchedComponentUnionPlaquetteSupport
        stretched background) :=
  presentedSeedUnionPlaquetteSupport_connected
    (certifiedStretchedLeftRootSeed stretched background)
    (certifiedStretchedRightRootSeed stretched background)
    (certifiedStretchedSeedRootPlaquettesAdjacent stretched background)

/-- The complete two-root union, with its exact physical peel budget and all
data needed by the padded rooted-animal compiler retained in `Type`. -/
def certifiedStretchedComponentUnionBoundedRootedAnimalData
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    BoundedRootedZ4AnimalData where
  root := slabPlaquetteAt 1
    (certifiedStretchedLeftRootCopy stretched).faceId
  support := certifiedStretchedComponentUnionPlaquetteSupport
    stretched background
  root_mem := certifiedStretchedLeftRootPlaquette_mem_unionSupport
    stretched background
  support_nodup := certifiedStretchedComponentUnionPlaquetteSupport_nodup
    stretched background
  connected := certifiedStretchedComponentUnionPlaquetteSupport_connected
    stretched background
  budget := (certifiedStretchedComponentUnionSupportedSelection
    stretched background).peelFaces.length
  support_length_le_budget :=
    certifiedStretchedComponentUnionPlaquetteSupport_length_le_peelFaces
      stretched background

/-! ## 2. Compile and pad at the exact physical peel budget -/

/-- The one-word shape code for the complete certified two-root union. -/
def certifiedStretchedComponentUnionPaddedTourCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    List (Fin (z4Chain.D + 1)) :=
  boundedRootedZ4AnimalPaddedTourCode
    (certifiedStretchedComponentUnionBoundedRootedAnimalData
      stretched background)

/-- Small transport boundary exposing the generic compiler call without
unfolding the completed dependent BF4 presentation downstream. -/
theorem certifiedStretchedComponentUnionPaddedTourCode_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedComponentUnionPaddedTourCode stretched background =
      boundedRootedZ4AnimalPaddedTourCode
        (certifiedStretchedComponentUnionBoundedRootedAnimalData
          stretched background) :=
  rfl

/-- The production word has exactly twice the physical peel length. -/
theorem certifiedStretchedComponentUnionPaddedTourCode_length
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (certifiedStretchedComponentUnionPaddedTourCode
      stretched background).length =
      2 * (certifiedStretchedComponentUnionBoundedRootedAnimalData
        stretched background).budget := by
  rw [certifiedStretchedComponentUnionPaddedTourCode_eq]
  exact boundedRootedZ4AnimalPaddedTourCode_length
    (certifiedStretchedComponentUnionBoundedRootedAnimalData
      stretched background)

/-- The production word belongs to the single carrier indexed by the physical
peel length. -/
theorem certifiedStretchedComponentUnionPaddedTourCode_mem_carrier
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedComponentUnionPaddedTourCode stretched background ∈
      rootedZ4AnimalPaddedTourCarrier
        (certifiedStretchedComponentUnionBoundedRootedAnimalData
          stretched background).budget := by
  rw [certifiedStretchedComponentUnionPaddedTourCode_eq]
  exact boundedRootedZ4AnimalPaddedTourCode_mem_carrier
    (certifiedStretchedComponentUnionBoundedRootedAnimalData
      stretched background)

/-- Decoding the production word recovers exactly the complete union support. -/
theorem certifiedStretchedComponentUnionPaddedTourCode_decode_sameSupport
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    sameSupport
      (certifiedStretchedComponentUnionBoundedRootedAnimalData
        stretched background).support
      (decode z4Chain
        (certifiedStretchedComponentUnionBoundedRootedAnimalData
          stretched background).root
        (certifiedStretchedComponentUnionPaddedTourCode
          stretched background)) := by
  rw [certifiedStretchedComponentUnionPaddedTourCode_eq]
  exact boundedRootedZ4AnimalPaddedTourCode_decode_sameSupport
    (certifiedStretchedComponentUnionBoundedRootedAnimalData
      stretched background)

/-- The common one-animal shape carrier has exactly the claimed entropy. -/
theorem certifiedStretchedComponentUnionPaddedTourCarrier_length
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (rootedZ4AnimalPaddedTourCarrier
      (certifiedStretchedComponentUnionBoundedRootedAnimalData
        stretched background).budget).length =
      625 ^ (certifiedStretchedComponentUnionBoundedRootedAnimalData
        stretched background).budget :=
  boundedRootedZ4AnimalPaddedTourCarrier_length
    (certifiedStretchedComponentUnionBoundedRootedAnimalData
      stretched background)

#print axioms certifiedStretchedSeedRootPlaquettesAdjacent
#print axioms certifiedStretchedComponentUnionPlaquetteSupport_connected
#print axioms certifiedStretchedComponentUnionBoundedRootedAnimalData
#print axioms certifiedStretchedComponentUnionPaddedTourCode
#print axioms certifiedStretchedComponentUnionPaddedTourCode_eq
#print axioms certifiedStretchedComponentUnionPaddedTourCode_length
#print axioms certifiedStretchedComponentUnionPaddedTourCode_mem_carrier
#print axioms certifiedStretchedComponentUnionPaddedTourCode_decode_sameSupport
#print axioms certifiedStretchedComponentUnionPaddedTourCarrier_length

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAnimalTourCode
