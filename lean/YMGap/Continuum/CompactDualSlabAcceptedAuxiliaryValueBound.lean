/-
# Accepted canonical auxiliary values are paid by incident physical mass

The production cutoff only gives the coarse estimate `auxiliary edge <= 6*K`.
For volume-independent inverse counting one needs the sharper, local statement:
every used channel in an accepted left-associated SU(2) fusion tree is at most
the total physical spin incident on that link.

The proof follows the literal canonical fusion chain at valence at most six.
At valences one and two the sole auxiliary terminator is forced to zero.  At
valences four through six, successive applications of the Clebsch--Gordan
triangle inequality bound each internal output by the physical prefix feeding
it, hence by the complete incident l1 mass.

Constructive contract: finite valence case analysis, explicit Boolean fusion
guards, and natural arithmetic only.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, noncomputable declaration, or enlarged
heartbeat budget.
-/

import YMGap.Continuum.CanonicalLinkAuxiliarySupportBound
import YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing

namespace YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-- Every used auxiliary edge of an accepted degree-at-most-six canonical
fusion chain is bounded by the l1 mass of all its external inputs. -/
theorem canonicalLinkConditionalAllowedB_auxiliary_le_external_l1
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (edge : Nat) (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates degree) :
    auxiliary edge <=
      natListSum
        ((List.finRange degree).map fun position => external position.val) := by
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
    have hzero : auxiliary 1 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    simp [hzero, natListSum, List.finRange]
  · have hedgeEq : edge = 2 := by
      simpa [canonicalUsedAuxiliaryCoordinates,
        canonicalUsedCoordinates] using hedge
    subst edge
    have hzero : auxiliary 2 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    simp [hzero, natListSum, List.finRange]
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · have hvertices :=
      canonicalLinkConditionalAllowedB_vertices_admissible
        4 external auxiliary hallowed
    have hparts :=
      (verticesAdmissibleB_cons_true_iff
        (0, 1, 5) [(5, 2, 3)]
        (canonicalLinkLabelling 4 external auxiliary)).mp hvertices
    have hfirst := fusionOK_output_le_add hparts.1
    simp [canonicalLinkLabelling, overlayOn] at hfirst
    simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    subst edge
    simp [natListSum, List.finRange]
    omega
  · have hvertices :=
      canonicalLinkConditionalAllowedB_vertices_admissible
        5 external auxiliary hallowed
    have hparts :=
      (verticesAdmissibleB_cons_true_iff
        (0, 1, 6) [(6, 2, 7), (7, 3, 4)]
        (canonicalLinkLabelling 5 external auxiliary)).mp hvertices
    have hfirst := fusionOK_output_le_add hparts.1
    have htail :=
      (verticesAdmissibleB_cons_true_iff
        (6, 2, 7) [(7, 3, 4)]
        (canonicalLinkLabelling 5 external auxiliary)).mp hparts.2
    have hsecond := fusionOK_output_le_add htail.1
    simp [canonicalLinkLabelling, overlayOn] at hfirst hsecond
    simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    rcases hedge with rfl | rfl <;>
      simp [natListSum, List.finRange] <;> omega
  · have hvertices :=
      canonicalLinkConditionalAllowedB_vertices_admissible
        6 external auxiliary hallowed
    have hparts :=
      (verticesAdmissibleB_cons_true_iff
        (0, 1, 7) [(7, 2, 8), (8, 3, 9), (9, 4, 5)]
        (canonicalLinkLabelling 6 external auxiliary)).mp hvertices
    have hfirst := fusionOK_output_le_add hparts.1
    have htailOne :=
      (verticesAdmissibleB_cons_true_iff
        (7, 2, 8) [(8, 3, 9), (9, 4, 5)]
        (canonicalLinkLabelling 6 external auxiliary)).mp hparts.2
    have hsecond := fusionOK_output_le_add htailOne.1
    have htailTwo :=
      (verticesAdmissibleB_cons_true_iff
        (8, 3, 9) [(9, 4, 5)]
        (canonicalLinkLabelling 6 external auxiliary)).mp htailOne.2
    have hthird := fusionOK_output_le_add htailTwo.1
    simp [canonicalLinkLabelling, overlayOn] at hfirst hsecond hthird
    simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    have hthree : external (3 : Fin 6).val = external 3 := by
      rfl
    rcases hedge with rfl | rfl | rfl <;>
      simp [natListSum, List.finRange, hthree] <;> omega

private theorem finRange_map_get {A : Type} (entries : List A) :
    (List.finRange entries.length).map entries.get = entries := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    (List.ofFn_getElem (xs := entries))

/-- Literal corrected-slab specialization: every used entry of an accepted
link-intertwiner witness is paid by the physical spin mass incident on that
link.  The estimate contains no cutoff factor. -/
theorem slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1
    {cutoff extent : Nat} {physical auxiliary : SlabLabelling}
    {link : SlabLink}
    (hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link)
    (edge : Nat)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length) :
    auxiliary edge <=
      natListSum ((slabIncidentPlaqIds extent link).map physical) := by
  have hlocal :=
    canonicalLinkConditionalAllowedB_auxiliary_le_external_l1
      (degree := (slabIncidentPlaqIds extent link).length)
      (external := slabLinkExternalSpins extent physical link)
      (auxiliary := auxiliary)
      (slabIncidentPlaqIds_length_le_six extent link)
      (slabLinkFusionWitness_mem_allowed
        cutoff extent physical link auxiliary hmem)
      edge hedge
  calc
    auxiliary edge <=
        natListSum
          ((List.finRange (slabIncidentPlaqIds extent link).length).map
            fun position =>
              slabLinkExternalSpins extent physical link position.val) :=
      hlocal
    _ = natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position =>
            physical ((slabIncidentPlaqIds extent link).get position)) := by
      apply natListSum_map_congr
      intro position _
      exact externalSpinsOfList_map_get
        (slabIncidentPlaqIds extent link) physical position
    _ = natListSum ((slabIncidentPlaqIds extent link).map physical) := by
      have hmapped := congrArg (List.map physical)
        (finRange_map_get (slabIncidentPlaqIds extent link))
      have hsum := congrArg natListSum hmapped
      simpa only [List.map_map, Function.comp_apply] using hsum

#print axioms canonicalLinkConditionalAllowedB_auxiliary_le_external_l1
#print axioms slabLinkFusionWitness_auxiliary_le_incidentPhysical_l1

end YMGap.Continuum.CompactDualSlabAcceptedAuxiliaryValueBound
