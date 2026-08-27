/-
# Decode adaptive component specifications and complete auxiliary rows

The adaptive auxiliary carrier is useful for inverse counting only if its
dependence on a production seed is itself controlled by the preceding finite
codes.  This module proves the two required literal left-inverse facts.

At a common root, equal shape and physical-multiplicity words give the same
physical drop at every face, hence the same incident mass at every complete
slab link and the same adaptive specification list.  Independently, equality
of the complete fixed-order row lists gives equality of the paired auxiliary
word tables used by the existing assignment reconstruction theorem.

Constructive contract: congruence over finite maps only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
import YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalDropDecoder
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPaddedAnimalTourCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentPhysicalMultiplicityCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- Pairing a fixed item list with two equal mapped value lists preserves
literal table equality. -/
theorem pairedMap_eq_of_map_eq
    {A B : Type} (left right : A -> B) : forall items : List A,
    items.map left = items.map right ->
      items.map (fun item => (item, left item)) =
        items.map (fun item => (item, right item))
  | [], _ => rfl
  | item :: items, heq => by
      have hparts :
          left item = right item ∧ items.map left = items.map right :=
        List.cons.inj heq
      simp only [List.map_cons]
      rw [hparts.1, pairedMap_eq_of_map_eq left right items hparts.2]

/-- Equal rooted shape and physical-multiplicity codes determine the same
link-adaptive mass/width specifications. -/
theorem componentProductionCodes_eq_adaptiveAuxiliarySpecifications_eq
    {K extent : Nat} {physical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hshape : componentPlaquettePaddedTourCode left =
      componentPlaquettePaddedTourCode right)
    (hmultiplicity : componentDecodedPhysicalMultiplicityBinaryCode left =
      componentDecodedPhysicalMultiplicityBinaryCode right) :
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications left =
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications right := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
  apply List.map_congr_left
  intro link hlink
  apply Prod.ext
  · unfold SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass
    apply congrArg natListSum
    apply List.map_congr_left
    intro faceId hfaceId
    exact componentProductionCodes_eq_physicalDrop_eq
      left right hroot hshape hmultiplicity faceId
  · rfl

/-- Equal complete adaptive row lists give equal paired auxiliary word tables
in the existing finite drop code. -/
theorem adaptiveAuxiliaryRows_eq_dropCode_auxiliaryWords_eq
    {K extent : Nat} {physical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hrows : SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows left =
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows right) :
    (SlabFusionWitnessFaceStrandSeed.dropCode left).auxiliaryWords =
      (SlabFusionWitnessFaceStrandSeed.dropCode right).auxiliaryWords := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows at hrows
  unfold SlabFusionWitnessFaceStrandSeed.dropCode
    slabAuxiliaryDropWordsFrom
  exact pairedMap_eq_of_map_eq
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt left)
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt right)
    (boundaryCompleteSlabLinks extent) hrows

/-- The three adaptive production words recover all data consumed by the
finite physical and auxiliary reconstruction maps. -/
theorem componentAdaptiveCodes_eq_dropData_eq
    {K extent : Nat} {physical : SlabLabelling}
    {leftAssignment rightAssignment : SlabFusionWitnessAssignment}
    {hleftAssignment : leftAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    {hrightAssignment : rightAssignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (left : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        leftAssignment hleftAssignment)
    (right : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        rightAssignment hrightAssignment)
    (hroot : left.root.faceId = right.root.faceId)
    (hshape : componentPlaquettePaddedTourCode left =
      componentPlaquettePaddedTourCode right)
    (hmultiplicity : componentDecodedPhysicalMultiplicityBinaryCode left =
      componentDecodedPhysicalMultiplicityBinaryCode right)
    (hrows : SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows left =
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows right) :
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications left =
        SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications right ∧
      (forall faceId,
        slabFaceStrandSelectionCount left.selected faceId =
          slabFaceStrandSelectionCount right.selected faceId) ∧
      (SlabFusionWitnessFaceStrandSeed.dropCode left).auxiliaryWords =
        (SlabFusionWitnessFaceStrandSeed.dropCode right).auxiliaryWords := by
  constructor
  · exact
      componentProductionCodes_eq_adaptiveAuxiliarySpecifications_eq
        left right hroot hshape hmultiplicity
  constructor
  · intro faceId
    exact componentProductionCodes_eq_physicalDrop_eq
      left right hroot hshape hmultiplicity faceId
  · exact adaptiveAuxiliaryRows_eq_dropCode_auxiliaryWords_eq
      left right hrows

#print axioms pairedMap_eq_of_map_eq
#print axioms componentProductionCodes_eq_adaptiveAuxiliarySpecifications_eq
#print axioms adaptiveAuxiliaryRows_eq_dropCode_auxiliaryWords_eq
#print axioms componentAdaptiveCodes_eq_dropData_eq

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryDecoder
