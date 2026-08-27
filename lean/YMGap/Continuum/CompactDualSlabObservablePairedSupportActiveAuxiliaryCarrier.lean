/-
# One volume-independent carrier for both source auxiliary fields

For every active paired-support link, record the used canonical auxiliary row
of the left source and then the corresponding row of the right source.  Each
row is given the exact incident physical l1 mass of its own replica as radix
budget.  The sharp accepted-channel bound puts the production row in that
adaptive carrier.

The combined specification mass is the paired active-link incident mass,
already bounded by four times the initial component mass.  Since every
canonical link has at most three used auxiliary coordinates, the abstract
adaptive-carrier estimate gives the single volume- and cutoff-independent
factor `4096^componentMass` for both source assignments together.

Constructive contract: literal source-assignment lookup, exact local fusion
bounds, finite maps, and natural arithmetic only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
import YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinkMass
import YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveAuxiliaryCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinkMass
open YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveLinks
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. One ordered coordinate for each active link and replica -/

/-- `false` writes the left source row and `true` writes the right source row. -/
abbrev SlabPairedActiveLinkCoordinate := SlabLink × Bool

/-- Two replica coordinates, in a fixed order, at every active link. -/
def slabObservablePairTargetSupportActiveLinkCoordinates
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List SlabPairedActiveLinkCoordinate :=
  (slabObservableTwoReplicaPairTargetSupportActiveLinks
    D pair targetFaceId).flatMap fun link => [(link, false), (link, true)]

theorem slabObservablePairTargetSupportActiveLinkCoordinate_link_mem
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    {coordinate : SlabPairedActiveLinkCoordinate}
    (hcoordinate : coordinate ∈
      slabObservablePairTargetSupportActiveLinkCoordinates
        D pair targetFaceId) :
    coordinate.1 ∈
      slabObservableTwoReplicaPairTargetSupportActiveLinks
        D pair targetFaceId := by
  unfold slabObservablePairTargetSupportActiveLinkCoordinates at hcoordinate
  obtain ⟨link, hlink, hblock⟩ := List.mem_flatMap.mp hcoordinate
  rcases List.mem_cons.mp hblock with hfirst | hrest
  · subst coordinate
    exact hlink
  · have hsecond := List.mem_singleton.mp hrest
    subst coordinate
    exact hlink

/-! ## 2. Exact link-adaptive specifications and production rows -/

/-- Physical incident mass of the selected source replica at one active
coordinate. -/
def slabObservablePairActiveAuxiliaryMassAt
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (coordinate : SlabPairedActiveLinkCoordinate) : Nat :=
  if coordinate.2 then
    natListSum
      ((slabIncidentPlaqIds D.extent coordinate.1).map pair.2.1.1)
  else
    natListSum
      ((slabIncidentPlaqIds D.extent coordinate.1).map pair.1.1.1)

/-- Number of used canonical auxiliary channels at the coordinate's link. -/
def slabObservablePairActiveAuxiliaryWidthAt
    (D : SlabPhysicalData)
    (coordinate : SlabPairedActiveLinkCoordinate) : Nat :=
  (canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds D.extent coordinate.1).length).length

/-- The literal source auxiliary row at one active link and replica. -/
def slabObservablePairActiveAuxiliaryRowAt
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (coordinate : SlabPairedActiveLinkCoordinate) : List Nat :=
  let auxiliary := if coordinate.2 then
      slabFusionWitnessAssignmentAt coordinate.1 pair.2.1.2
    else slabFusionWitnessAssignmentAt coordinate.1 pair.1.1.2
  (canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds D.extent coordinate.1).length).map auxiliary

/-- The combined adaptive specification list for both source assignments. -/
def slabObservablePairTargetSupportActiveAuxiliarySpecifications
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List (Nat × Nat) :=
  (slabObservablePairTargetSupportActiveLinkCoordinates
    D pair targetFaceId).map fun coordinate =>
      (slabObservablePairActiveAuxiliaryMassAt D pair coordinate,
        slabObservablePairActiveAuxiliaryWidthAt D coordinate)

/-- Both literal production row tables in the matching coordinate order. -/
def slabObservablePairTargetSupportActiveAuxiliaryRows
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List (List Nat) :=
  (slabObservablePairTargetSupportActiveLinkCoordinates
    D pair targetFaceId).map
      (slabObservablePairActiveAuxiliaryRowAt D pair)

/-- Every stored production row fits its exact replica-local physical mass
and canonical width. -/
theorem slabObservablePairTargetSupportActiveAuxiliaryRows_fit
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    AdaptiveAuxiliaryRowsFit
      (slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D pair targetFaceId)
      (slabObservablePairTargetSupportActiveAuxiliaryRows
        D pair targetFaceId) := by
  unfold slabObservablePairTargetSupportActiveAuxiliarySpecifications
    slabObservablePairTargetSupportActiveAuxiliaryRows
  apply adaptiveAuxiliaryRowsFit_map
  · intro coordinate _
    unfold slabObservablePairActiveAuxiliaryRowAt
      slabObservablePairActiveAuxiliaryWidthAt
    rw [List.length_map]
  · intro coordinate hcoordinate value hvalue
    unfold slabObservablePairActiveAuxiliaryRowAt at hvalue
    obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
    have hactive :=
      slabObservablePairTargetSupportActiveLinkCoordinate_link_mem
        D pair hcoordinate
    have hcomplete :=
      slabObservableTwoReplicaPairTargetSupportActiveLink_mem_complete
        D pair hactive
    cases hside : coordinate.2 with
    | false =>
        have hlocal := slabFusionWitnessAssignmentAt_mem_local
          D.cutoff D.extent pair.1.1.1
          (boundaryCompleteSlabLinks D.extent) pair.1.1.2
          pair.1.assignment_mem coordinate.1 hcomplete
        have hbound :=
          slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
            hlocal edge hedge
        unfold slabObservablePairActiveAuxiliaryMassAt
        rw [hside]
        exact Nat.lt_succ_of_le hbound
    | true =>
        have hrightAssignment : pair.2.1.2 ∈
            slabFusionWitnessAssignmentsOn D.cutoff D.extent pair.2.1.1
              (boundaryCompleteSlabLinks D.extent) :=
          (mem_slabExpandedFineSources_iff.mp pair.2.2).2
        have hlocal := slabFusionWitnessAssignmentAt_mem_local
          D.cutoff D.extent pair.2.1.1
          (boundaryCompleteSlabLinks D.extent) pair.2.1.2
          hrightAssignment coordinate.1 hcomplete
        have hbound :=
          slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
            hlocal edge hedge
        unfold slabObservablePairActiveAuxiliaryMassAt
        rw [hside]
        exact Nat.lt_succ_of_le hbound

/-! ## 3. Combined mass and carrier bounds -/

private theorem adaptiveAuxiliaryMass_map_eq_natListSum
    {A : Type} (mass width : A → Nat) : ∀ items : List A,
    adaptiveAuxiliaryMass
        (items.map fun item => (mass item, width item)) =
      natListSum (items.map mass)
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, adaptiveAuxiliaryMass, natListSum]
      rw [adaptiveAuxiliaryMass_map_eq_natListSum mass width tail]

private theorem activeCoordinateMass_eq_pairIncidentMass
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    ∀ links : List SlabLink,
    natListSum
        (((links.flatMap fun link => [(link, false), (link, true)]).map
          (slabObservablePairActiveAuxiliaryMassAt D pair))) =
      natListSum (links.map fun link =>
        natListSum
          ((slabIncidentPlaqIds D.extent link).map fun faceId =>
            pair.1.1.1 faceId + pair.2.1.1 faceId))
  | [] => rfl
  | link :: tail => by
      rw [List.flatMap_cons, List.map_append, natListSum_append]
      simp only [List.map_cons, List.map_nil, natListSum]
      rw [activeCoordinateMass_eq_pairIncidentMass D pair tail]
      unfold slabObservablePairActiveAuxiliaryMassAt
      simp only [Bool.false_eq_true, if_false, if_true]
      have hadd :
          natListSum ((slabIncidentPlaqIds D.extent link).map pair.1.1.1) +
              natListSum ((slabIncidentPlaqIds D.extent link).map pair.2.1.1) =
            natListSum
              ((slabIncidentPlaqIds D.extent link).map fun faceId =>
                pair.1.1.1 faceId + pair.2.1.1 faceId) := by
        induction slabIncidentPlaqIds D.extent link with
        | nil => rfl
        | cons faceId rest ih =>
            simp only [List.map_cons, natListSum]
            omega
      omega

/-- The combined specification mass is bounded by four times the paired
physical component mass. -/
theorem slabObservablePairTargetSupportActiveAuxiliaryMass_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    adaptiveAuxiliaryMass
        (slabObservablePairTargetSupportActiveAuxiliarySpecifications
          D pair targetFaceId) ≤
      4 * slabObservableTwoReplicaPairTargetSupportMass
        D pair targetFaceId := by
  unfold slabObservablePairTargetSupportActiveAuxiliarySpecifications
  rw [adaptiveAuxiliaryMass_map_eq_natListSum]
  unfold slabObservablePairTargetSupportActiveLinkCoordinates
  rw [activeCoordinateMass_eq_pairIncidentMass]
  exact activeLinks_incidentPairMass_le_four_mul_componentMass
    D rootFaceId targetFaceId htarget pair hpair

/-- Every combined source specification has canonical width at most three. -/
theorem slabObservablePairTargetSupportActiveAuxiliarySpecifications_width_le_three
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (specification : Nat × Nat)
    (hspecification : specification ∈
      slabObservablePairTargetSupportActiveAuxiliarySpecifications
        D pair targetFaceId) :
    specification.2 ≤ 3 := by
  unfold slabObservablePairTargetSupportActiveAuxiliarySpecifications
    at hspecification
  obtain ⟨coordinate, _, rfl⟩ := List.mem_map.mp hspecification
  exact canonicalUsedAuxiliaryCoordinates_length_le_three
    (slabIncidentPlaqIds_length_le_six D.extent coordinate.1)

/-- The aggregate adaptive carrier for both source auxiliary fields. -/
def slabObservablePairTargetSupportActiveAuxiliaryCarrier
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (targetFaceId : Nat) : List (List (List Nat)) :=
  adaptiveAuxiliaryCarrier
    (slabObservablePairTargetSupportActiveAuxiliarySpecifications
      D pair targetFaceId)

theorem slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
    (D : SlabPhysicalData) {rootFaceId targetFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    slabObservablePairTargetSupportActiveAuxiliaryRows
        D pair targetFaceId ∈
      slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D pair targetFaceId :=
  (slabObservablePairTargetSupportActiveAuxiliaryRows_fit
    D pair).mem_carrier

/-- **Aggregate auxiliary entropy bound.**  Both source assignments together
cost at most `4096^M`, where `M` is their physical mass on the one initial
target component. -/
theorem slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (pair : SlabObservableTwoReplicaPair D rootFaceId)
    (hpair : pair ∈ slabObservableFourCellSourcePairs
      D rootFaceId targetFaceId) :
    (slabObservablePairTargetSupportActiveAuxiliaryCarrier
        D pair targetFaceId).length ≤
      4096 ^ slabObservableTwoReplicaPairTargetSupportMass
        D pair targetFaceId := by
  unfold slabObservablePairTargetSupportActiveAuxiliaryCarrier
  apply adaptiveAuxiliaryCarrier_length_le_4096_pow
  · exact
      slabObservablePairTargetSupportActiveAuxiliarySpecifications_width_le_three
        D pair
  · exact slabObservablePairTargetSupportActiveAuxiliaryMass_le
      D rootFaceId targetFaceId htarget pair hpair

#print axioms slabObservablePairTargetSupportActiveLinkCoordinates
#print axioms slabObservablePairTargetSupportActiveAuxiliarySpecifications
#print axioms slabObservablePairTargetSupportActiveAuxiliaryRows
#print axioms slabObservablePairTargetSupportActiveAuxiliaryRows_fit
#print axioms slabObservablePairTargetSupportActiveAuxiliaryMass_le
#print axioms slabObservablePairTargetSupportActiveAuxiliaryCarrier
#print axioms slabObservablePairTargetSupportActiveAuxiliaryRows_mem_carrier
#print axioms slabObservablePairTargetSupportActiveAuxiliaryCarrier_length_le

end YMGap.Continuum.CompactDualSlabObservablePairedSupportActiveAuxiliaryCarrier
