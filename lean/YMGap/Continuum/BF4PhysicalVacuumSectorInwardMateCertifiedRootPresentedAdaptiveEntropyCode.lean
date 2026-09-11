/-
# The certified stretched-root source enters the common adaptive carrier

The connected shape and physical words now reconstruct the complete selected
physical drop.  Hence they determine every link mass used by the existing
adaptive auxiliary carrier.  The retained presented face order determines the
row width and remains part of the lowered target.

This module packages the actual certified shape word, physical multiplicity
word, and complete presented auxiliary-row table as one
`ComponentAdaptiveEntropyCode`.  It proves membership in the common carrier
indexed only by extent, root face, and physical peel size.  That carrier is
already bounded by

  `(625 * 4 * 4096) ^ peelSize = 10240000 ^ peelSize`,

whose one-step anchor ratio is exactly `8/25 < 1`.

This is the common-carrier theorem, not yet the fixed-lowered-target
injectivity theorem.  No `Classical`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, enlarged heartbeat budget, or trusted
external computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabDecodedPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.RootedZ4AnimalPaddedTourCode
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The prior structural words determine the adaptive specification -/

/-- The physical mass decoded from the two structural words is exactly the
stored physical peel budget. -/
theorem certifiedStretchedComponentUnionAdaptiveDecodedPhysicalMass_eq_budget
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    componentAdaptiveDecodedPhysicalMass 1
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).rootFaceId
        (certifiedStretchedComponentUnionConnectedShapeCode
          stretched background)
        (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
          stretched background) =
      (certifiedStretchedComponentUnionShapePhysicalData
        stretched background).budget := by
  unfold componentAdaptiveDecodedPhysicalMass
  change natListSum ((slabPhysicalFaceEdges 1).map
      (componentPhysicalDropDecode 1
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).rootFaceId
        (certifiedStretchedComponentUnionConnectedShapeCode
          stretched background)
        (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
          stretched background))) =
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background).peelFaces.length
  calc
    natListSum ((slabPhysicalFaceEdges 1).map
        (componentPhysicalDropDecode 1
          (certifiedStretchedComponentUnionShapePhysicalData
            stretched background).rootFaceId
          (certifiedStretchedComponentUnionConnectedShapeCode
            stretched background)
          (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
            stretched background))) =
        natListSum ((slabPhysicalFaceEdges 1).map
          (slabFaceStrandSelectionCount
            (certifiedStretchedComponentUnionSupportedSelection
              stretched background).closed.selected)) := by
      apply natListSum_map_congr
      intro faceId hfaceId
      exact certifiedStretchedComponentUnionPhysicalDropDecode
        stretched background faceId
    _ = (certifiedStretchedComponentUnionSupportedSelection
        stretched background).peelFaces.length :=
      (presentedSelection_peelFaces_length_eq_physicalDrop_l1
        (certifiedStretchedComponentUnionSupportedSelection
          stretched background)).symm

/-- Therefore the connected structural pair passes the common carrier's
decoded-mass filter. -/
theorem certifiedStretchedComponentUnionAdaptiveMultiplicityAdmissible
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    componentAdaptiveMultiplicityAdmissibleB 1
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).rootFaceId
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).budget
        (certifiedStretchedComponentUnionConnectedShapeCode
          stretched background)
        (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
          stretched background) = true := by
  unfold componentAdaptiveMultiplicityAdmissibleB
  simp only [decide_eq_true_eq]
  rw [certifiedStretchedComponentUnionAdaptiveDecodedPhysicalMass_eq_budget]
  exact Nat.le_refl _

/-- The preceding two words decode the literal presented auxiliary
specification: physical mass from the words, row width from the retained face
order. -/
theorem certifiedStretchedComponentUnionAdaptiveSpecificationsDecode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    componentAdaptiveSpecificationsDecode 1
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).rootFaceId
        (certifiedStretchedComponentUnionConnectedShapeCode
          stretched background)
        (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
          stretched background) =
      presentedSelectionAdaptiveAuxiliarySpecifications
        (certifiedStretchedComponentUnionSupportedSelection
          stretched background) := by
  unfold componentAdaptiveSpecificationsDecode
    presentedSelectionAdaptiveAuxiliarySpecifications
  apply List.map_congr_left
  intro link hlink
  apply Prod.ext
  · unfold presentedSelectionLinkPhysicalMass
    apply natListSum_map_congr
    intro faceId hfaceId
    exact certifiedStretchedComponentUnionPhysicalDropDecode
      stretched background faceId
  · rw [presentedSlabSupportedSelectionAuxiliaryDropWordAt_of_mem
      (certifiedStretchedComponentUnionSupportedSelection
        stretched background) link hlink,
      List.length_map]
    have hlength :=
      (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded stretched.certified background
          ⟨link, hlink⟩).order.production_perm.length_eq
    rw [hlength]

/-! ## 2. The actual three-word code and common-carrier membership -/

/-- A shallow name for the complete presented auxiliary row word.  Keeping
this projection boundary opaque prevents downstream equality proofs from
normalizing the complete certified strand graph. -/
def certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) : List (List Nat) :=
  presentedSelectionAdaptiveAuxiliaryRows
    (certifiedStretchedComponentUnionSupportedSelection
      stretched background)

/-- The complete adaptive code emitted by the certified two-root source. -/
def componentAdaptiveEntropyCodeOfWords
    (shape : List (Fin (z4Chain.D + 1)))
    (physicalMultiplicity : List Nat)
    (auxiliaryRows : List (List Nat)) : ComponentAdaptiveEntropyCode where
  shape := shape
  physicalMultiplicity := physicalMultiplicity
  auxiliaryRows := auxiliaryRows

@[simp] theorem componentAdaptiveEntropyCodeOfWords_shape
    (shape : List (Fin (z4Chain.D + 1)))
    (physicalMultiplicity : List Nat)
    (auxiliaryRows : List (List Nat)) :
    (componentAdaptiveEntropyCodeOfWords
      shape physicalMultiplicity auxiliaryRows).shape = shape := rfl

@[simp] theorem componentAdaptiveEntropyCodeOfWords_physicalMultiplicity
    (shape : List (Fin (z4Chain.D + 1)))
    (physicalMultiplicity : List Nat)
    (auxiliaryRows : List (List Nat)) :
    (componentAdaptiveEntropyCodeOfWords
      shape physicalMultiplicity auxiliaryRows).physicalMultiplicity =
        physicalMultiplicity := rfl

@[simp] theorem componentAdaptiveEntropyCodeOfWords_auxiliaryRows
    (shape : List (Fin (z4Chain.D + 1)))
    (physicalMultiplicity : List Nat)
    (auxiliaryRows : List (List Nat)) :
    (componentAdaptiveEntropyCodeOfWords
      shape physicalMultiplicity auxiliaryRows).auxiliaryRows =
        auxiliaryRows := rfl

/-- The complete adaptive code emitted by the certified two-root source. -/
def certifiedStretchedComponentUnionAdaptiveEntropyCode
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    ComponentAdaptiveEntropyCode :=
  componentAdaptiveEntropyCodeOfWords
    (certifiedStretchedComponentUnionConnectedShapeCode
      stretched background)
    (certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
      stretched background)
    (certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
      stretched background)

/-- The actual certified code lies in one common carrier indexed only by the
root and physical peel budget. -/
theorem certifiedStretchedComponentUnionAdaptiveEntropyCode_mem_carrier
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    certifiedStretchedComponentUnionAdaptiveEntropyCode stretched background ∈
      componentAdaptiveEntropyCarrier 1
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).rootFaceId
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).budget := by
  unfold componentAdaptiveEntropyCarrier
    certifiedStretchedComponentUnionAdaptiveEntropyCode
    componentAdaptiveEntropyCodeOfWords
    certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
  apply List.mem_flatMap.mpr
  refine ⟨certifiedStretchedComponentUnionConnectedShapeCode
    stretched background, ?_, ?_⟩
  · exact certifiedStretchedComponentUnionConnectedShapeCode_mem_carrier
      stretched background
  · apply List.mem_flatMap.mpr
    refine ⟨certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
      stretched background, ?_, ?_⟩
    · unfold componentAdaptivePhysicalCarrier
      apply List.mem_filter.mpr
      exact ⟨
        certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode_mem_carrier
          stretched background,
        certifiedStretchedComponentUnionAdaptiveMultiplicityAdmissible
          stretched background⟩
    · apply List.mem_map.mpr
      refine ⟨presentedSelectionAdaptiveAuxiliaryRows
        (certifiedStretchedComponentUnionSupportedSelection
          stretched background), ?_, rfl⟩
      rw [certifiedStretchedComponentUnionAdaptiveSpecificationsDecode]
      exact presentedSelectionAdaptiveAuxiliaryRows_mem_carrier
        (certifiedStretchedComponentUnionSupportedSelection
          stretched background)

/-! ## 3. Uniform entropy and strict reserve -/

/-- The common carrier containing the production code is bounded by the
strict adaptive entropy base. -/
theorem certifiedStretchedComponentUnionAdaptiveEntropyCarrier_length_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 <= K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (stretched : CubeInwardMateCertifiedFirstStretchedSource
      K physical hK hbounded)
    (background : PresentedSlabFusionWitnessAssignment
      K 1 physical (boundaryCompleteSlabLinks 1)) :
    (componentAdaptiveEntropyCarrier 1
      (certifiedStretchedComponentUnionShapePhysicalData
        stretched background).rootFaceId
      (certifiedStretchedComponentUnionShapePhysicalData
        stretched background).budget).length <=
      componentAdaptiveEntropyBase ^
        (certifiedStretchedComponentUnionShapePhysicalData
          stretched background).budget :=
  componentAdaptiveEntropyCarrier_length_le _ _ _

/-- The certified route inherits the exact strict entropy/anchor reserve
`8/25 < 1`. -/
theorem certifiedStretchedComponentUnionAdaptiveEntropyAnchorRatio_lt_one :
    componentAdaptiveEntropyAnchorRatio < (1 : Q') :=
  componentAdaptiveEntropyAnchorRatio_lt_one

#print axioms certifiedStretchedComponentUnionAdaptiveDecodedPhysicalMass_eq_budget
#print axioms certifiedStretchedComponentUnionAdaptiveMultiplicityAdmissible
#print axioms certifiedStretchedComponentUnionAdaptiveSpecificationsDecode
#print axioms certifiedStretchedComponentUnionAdaptiveEntropyCode
#print axioms certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
#print axioms componentAdaptiveEntropyCodeOfWords
#print axioms componentAdaptiveEntropyCodeOfWords_shape
#print axioms componentAdaptiveEntropyCodeOfWords_physicalMultiplicity
#print axioms componentAdaptiveEntropyCodeOfWords_auxiliaryRows
#print axioms certifiedStretchedComponentUnionAdaptiveEntropyCode_mem_carrier
#print axioms certifiedStretchedComponentUnionAdaptiveEntropyCarrier_length_le
#print axioms certifiedStretchedComponentUnionAdaptiveEntropyAnchorRatio_lt_one

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode
