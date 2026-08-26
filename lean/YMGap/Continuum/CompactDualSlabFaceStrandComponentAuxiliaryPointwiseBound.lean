/-
# A sharp pointwise bound for component auxiliary drops

The previous local estimate bounded the sum of the at most three canonical
auxiliary drops by three times the physical input mass.  For inverse counting
one needs the sharper coordinatewise fact: every internal edge of the
left-associated fusion tree carries at most the total selected physical input
mass at that link.

For degrees four through six this follows along the literal fusion chain:
each new internal output is bounded by the preceding internal input plus the
next physical input.  Degrees one and two contain only the forced-zero vacuum
terminator, and degree three has no auxiliary coordinate.

Constructive contract: the existing Kirchhoff inequalities, the explicit
degree-zero-through-six resolver, and natural arithmetic only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
import YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentGlobalAuxiliaryL1
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- Every used auxiliary edge of the degree-at-most-six canonical fusion
chain carries no more selected strands than the total physical input mass. -/
theorem canonicalLinkSelection_auxiliaryDrop_le_physical_l1
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed).resolved)
    (edge : Nat) (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates degree) :
    selection.drop edge <=
      natListSum
        ((List.finRange degree).map fun position =>
          selection.drop position.val) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · have hedgeEq : edge = 1 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    subst edge
    have hzeroAux : auxiliary 1 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    have hdrop :=
      ResolvedNetworkMateClosedSelection.drop_le_label selection 1
    have hlabel : canonicalLinkLabelling 1 external auxiliary 1 = 0 := by
      unfold canonicalLinkLabelling overlayOn
      simp [hzeroAux]
    rw [hlabel] at hdrop
    simp [natListSum, List.finRange]
    omega
  · have hedgeEq : edge = 2 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    subst edge
    have hzeroAux : auxiliary 2 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    have hdrop :=
      ResolvedNetworkMateClosedSelection.drop_le_label selection 2
    have hlabel : canonicalLinkLabelling 2 external auxiliary 2 = 0 := by
      unfold canonicalLinkLabelling overlayOn
      simp [hzeroAux]
    rw [hlabel] at hdrop
    simp [natListSum, List.finRange]
    omega
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · have hedgeEq : edge = 5 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    subst edge
    have hfirst :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 4 external auxiliary hallowed)
        selection (0, 1, 5) (by decide)
    simp at hfirst
    simp [natListSum, List.finRange]
    omega
  · have hedgeCases : edge = 6 ∨ edge = 7 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    have hfirst :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 5 external auxiliary hallowed)
        selection (0, 1, 6) (by decide)
    have hsecond :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 5 external auxiliary hallowed)
        selection (6, 2, 7) (by decide)
    simp at hfirst hsecond
    rcases hedgeCases with rfl | rfl <;>
      simp [natListSum, List.finRange] <;> omega
  · have hedgeCases : edge = 7 ∨ edge = 8 ∨ edge = 9 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    have hfirst :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
        selection (0, 1, 7) (by decide)
    have hsecond :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
        selection (7, 2, 8) (by decide)
    have hthird :=
      ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
        (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
        selection (8, 3, 9) (by decide)
    simp at hfirst hsecond hthird
    have hthree : selection.drop (3 : Fin 6).val =
        selection.drop 3 := by
      rfl
    rcases hedgeCases with rfl | rfl | rfl <;>
      simp [natListSum, List.finRange, hthree] <;> omega

/-- Literal corrected-slab specialization of the sharp pointwise bound. -/
theorem SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_le_physicalDrop_l1
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (edge : Nat)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length) :
    selection.drop edge <=
      natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.drop position.val) := by
  have hbound := canonicalLinkSelection_auxiliaryDrop_le_physical_l1
    (degree := (slabIncidentPlaqIds extent link).length)
    (external := slabLinkExternalSpins extent physical link)
    (auxiliary := auxiliary)
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem)
    selection.toMateClosedSelection edge hedge
  have hdrop :=
    SlabLinkPartnerClosedFaceSelection.toMateClosedSelection_drop selection
  calc
    selection.drop edge = selection.toMateClosedSelection.drop edge :=
      congrArg (fun drop => drop edge) hdrop.symm
    _ <= natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.toMateClosedSelection.drop position.val) :=
      hbound
    _ = natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.drop position.val) :=
      congrArg
        (fun drop => natListSum
          ((List.finRange (slabIncidentPlaqIds extent link).length).map
            fun position => drop position.val)) hdrop

/-- Every entry of a rooted component's literal auxiliary word is bounded by
the selected physical face mass incident on that link. -/
theorem SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_entry_le_incidentFace_l1
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links)
    (value : Nat)
    (hvalue : value ∈
      SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link) :
    value <= natListSum
      ((slabIncidentPlaqIds extent link).map fun faceId =>
        slabFaceStrandSelectionCount seed.selected faceId) := by
  rw [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
    seed link hlink] at hvalue
  obtain ⟨edge, hedge, rfl⟩ := List.mem_map.mp hvalue
  let selection := seed.atLinkSelection ⟨link, hlink⟩
  have hbound :=
    SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_le_physicalDrop_l1
      selection edge hedge
  have hmass :=
    SlabLinkPartnerClosedFaceSelection.physicalDrop_l1_eq_incidentFace_l1
      selection
  rw [hmass] at hbound
  exact hbound

#print axioms canonicalLinkSelection_auxiliaryDrop_le_physical_l1
#print axioms SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_le_physicalDrop_l1
#print axioms SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_entry_le_incidentFace_l1

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryPointwiseBound
