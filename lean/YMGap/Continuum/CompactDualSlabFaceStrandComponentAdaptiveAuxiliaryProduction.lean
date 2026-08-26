/-
# Production component rows inhabit the link-adaptive carrier

Use the complete corrected-slab link list, but give each link a word carrier
whose radix is determined by the selected physical mass at that link.  Links
outside the component have mass zero and therefore contribute a singleton
carrier, so retaining them introduces no volume factor and removes the need
for a separate sparse-row presence word.

The sharp pointwise theorem puts every production auxiliary entry below the
link radix.  The existing complete-slab incidence double count proves that
the total of the link masses is exactly four times the physical peel length.
The abstract adaptive-carrier theorem then gives the cutoff- and
volume-independent bound `4096^peelSize`.

Constructive contract: finite maps, the proved local Kirchhoff bound, and the
proved incidence permutation only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
import YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- Selected physical input mass presented at one literal slab link. -/
def SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (link : SlabLink) : Nat :=
  natListSum ((slabIncidentPlaqIds extent link).map fun faceId =>
    slabFaceStrandSelectionCount seed.selected faceId)

/-- One `(mass,width)` specification for every complete-slab link. -/
def SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List (Nat × Nat) :=
  (boundaryCompleteSlabLinks extent).map fun link =>
    (SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass seed link,
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length).length)

/-- The complete production auxiliary rows in the same fixed link order. -/
def SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List (List Nat) :=
  (boundaryCompleteSlabLinks extent).map
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)

/-- The link-adaptive Cartesian carrier attached to the component's decoded
physical drop profile. -/
def SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) : List (List (List Nat)) :=
  YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier.adaptiveAuxiliaryCarrier
    (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications seed)

/-- Every complete production row table satisfies its linkwise adaptive
specifications. -/
theorem SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_fit
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    AdaptiveAuxiliaryRowsFit
      (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications seed)
      (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows seed) := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows
  apply adaptiveAuxiliaryRowsFit_map
  · intro link hlink
    rw [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
      seed link hlink, List.length_map]
  · intro link hlink value hvalue
    have hbound :=
      SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_entry_le_incidentFace_l1
        seed link hlink value hvalue
    change value <
      SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass seed link + 1
    exact Nat.lt_succ_of_le hbound

/-- Hence every production row table belongs to its adaptive carrier. -/
theorem SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_mem_carrier
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows seed ∈
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier seed :=
  (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_fit seed).mem_carrier

private theorem adaptiveAuxiliaryMass_map_eq_natListSum
    (mass width : SlabLink -> Nat) : forall links : List SlabLink,
    adaptiveAuxiliaryMass
        (links.map fun link => (mass link, width link)) =
      natListSum (links.map mass)
  | [] => rfl
  | _ :: links => by
      simp only [List.map_cons, adaptiveAuxiliaryMass, natListSum]
      rw [adaptiveAuxiliaryMass_map_eq_natListSum mass width links]

/-- The specification mass is exactly four times the physical peel length. -/
theorem SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryMass_eq_four_mul_peelFaces
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    adaptiveAuxiliaryMass
        (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications seed) =
      4 * (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
  rw [adaptiveAuxiliaryMass_map_eq_natListSum]
  unfold SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass
  rw [slabLinkIncidentWeightSum_eq_four_mul_physicalWeightSum extent]
  rw [← SlabFusionWitnessFaceStrandSeed.peelFaces_length_eq_physicalDrop_l1
    seed]

/-- Every production link specification has one of the at most three used
canonical auxiliary coordinates. -/
theorem SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications_width_le_three
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment)
    (specification : Nat × Nat)
    (hspecification : specification ∈
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications seed) :
    specification.2 <= 3 := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
    at hspecification
  obtain ⟨link, _, rfl⟩ := List.mem_map.mp hspecification
  exact canonicalUsedAuxiliaryCoordinates_length_le_three
    (slabIncidentPlaqIds_length_le_six extent link)

/-- **Production auxiliary entropy bound.**  Although the row list ranges
over every volume link, zero-mass links contribute singleton carriers, and
the complete carrier has size at most `4096^peelSize`. -/
theorem SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier_length_le
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier seed).length <=
      4096 ^ (SlabFusionWitnessFaceStrandSeed.peelFaces seed).length := by
  unfold SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier
  apply adaptiveAuxiliaryCarrier_length_le_4096_pow
  · exact
      SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications_width_le_three
        seed
  · rw [SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryMass_eq_four_mul_peelFaces
      seed]
    exact Nat.le_refl _

#print axioms SlabFusionWitnessFaceStrandSeed.componentLinkPhysicalMass
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_fit
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryRows_mem_carrier
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryMass_eq_four_mul_peelFaces
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliarySpecifications_width_le_three
#print axioms SlabFusionWitnessFaceStrandSeed.adaptiveAuxiliaryCarrier_length_le

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryProduction
