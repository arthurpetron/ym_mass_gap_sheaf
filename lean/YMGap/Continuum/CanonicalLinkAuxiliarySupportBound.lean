/-
# Sharp production-cutoff support for canonical SU(2) link channels

An accepted canonical link resolver of valence at most six has at most three
genuine internal fusion channels.  If every external spin is at most `K`,
then each used auxiliary coordinate is already at most the production window
`6*K`.  Thus additive recombination of accepted subnetworks can be returned
to the original production cutoff once its recombined external boundary is
known to remain bounded by `K`; the generic `K+K` enumeration window is not
needed.

The proof is the literal valence-zero-through-six canonical chain.  Degrees
one and two contain only the forced-zero vacuum terminator.  At degrees four
through six, repeated use of the Clebsch--Gordan triangle inequality bounds
the successive channels by `2*K`, `3*K`, and `4*K`, respectively.

Constructive contract: finite case analysis and natural arithmetic only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
`noncomputable`, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
import YMGap.Continuum.SU2FusionSupportAddition

namespace YMGap.Continuum.CanonicalLinkAuxiliarySupportBound

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

private theorem canonicalLinkAuxiliarySupport_degree_four
    {K : Nat} {external auxiliary : EdgeLabelling}
    (hexternal : ∀ position : Fin 4, external position.val ≤ K)
    (hallowed :
      canonicalLinkConditionalAllowedB 4 external auxiliary = true)
    {edge : Nat}
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates 4) :
    auxiliary edge ≤ linkAuxiliaryCutoff K := by
  have hvertices :=
    canonicalLinkConditionalAllowedB_vertices_admissible
      4 external auxiliary hallowed
  have hparts :=
    (verticesAdmissibleB_cons_true_iff
      (0, 1, 5) [(5, 2, 3)]
      (canonicalLinkLabelling 4 external auxiliary)).mp hvertices
  have hfirst := fusionOK_output_le_add hparts.1
  simp [canonicalLinkLabelling, overlayOn] at hfirst
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  subst edge
  have hzero := hexternal ⟨0, by omega⟩
  have hone := hexternal ⟨1, by omega⟩
  change external 0 ≤ K at hzero
  change external 1 ≤ K at hone
  unfold linkAuxiliaryCutoff linkIncidenceBound
  omega

private theorem canonicalLinkAuxiliarySupport_degree_five
    {K : Nat} {external auxiliary : EdgeLabelling}
    (hexternal : ∀ position : Fin 5, external position.val ≤ K)
    (hallowed :
      canonicalLinkConditionalAllowedB 5 external auxiliary = true)
    {edge : Nat}
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates 5) :
    auxiliary edge ≤ linkAuxiliaryCutoff K := by
  have hvertices :=
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
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  have hzero := hexternal ⟨0, by omega⟩
  have hone := hexternal ⟨1, by omega⟩
  have htwo := hexternal ⟨2, by omega⟩
  change external 0 ≤ K at hzero
  change external 1 ≤ K at hone
  change external 2 ≤ K at htwo
  unfold linkAuxiliaryCutoff linkIncidenceBound
  rcases hedge with rfl | rfl <;> omega

private theorem canonicalLinkAuxiliarySupport_degree_six
    {K : Nat} {external auxiliary : EdgeLabelling}
    (hexternal : ∀ position : Fin 6, external position.val ≤ K)
    (hallowed :
      canonicalLinkConditionalAllowedB 6 external auxiliary = true)
    {edge : Nat}
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates 6) :
    auxiliary edge ≤ linkAuxiliaryCutoff K := by
  have hvertices :=
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
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates] at hedge
  have hzero := hexternal ⟨0, by omega⟩
  have hone := hexternal ⟨1, by omega⟩
  have htwo := hexternal ⟨2, by omega⟩
  have hthree := hexternal ⟨3, by omega⟩
  change external 0 ≤ K at hzero
  change external 1 ≤ K at hone
  change external 2 ≤ K at htwo
  change external 3 ≤ K at hthree
  unfold linkAuxiliaryCutoff linkIncidenceBound
  rcases hedge with rfl | rfl | rfl <;> omega

/-- Every used auxiliary coordinate of an accepted canonical resolver stays
inside the original production window `6*K`, provided the recombined external
labels stay bounded by `K`. -/
theorem canonicalLinkConditionalAllowedB_auxiliary_le_linkAuxiliaryCutoff
    {K degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hexternal : ∀ position : Fin degree, external position.val ≤ K)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    {edge : Nat}
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates degree) :
    auxiliary edge ≤ linkAuxiliaryCutoff K := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · have hzero : auxiliary 1 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    subst edge
    simp [hzero]
  · have hzero : auxiliary 2 = 0 :=
      canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
        (by decide) hallowed
    simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
    subst edge
    simp [hzero]
  · simp [canonicalUsedAuxiliaryCoordinates,
      canonicalUsedCoordinates] at hedge
  · exact canonicalLinkAuxiliarySupport_degree_four
      hexternal hallowed hedge
  · exact canonicalLinkAuxiliarySupport_degree_five
      hexternal hallowed hedge
  · exact canonicalLinkAuxiliarySupport_degree_six
      hexternal hallowed hedge

#print axioms canonicalLinkConditionalAllowedB_auxiliary_le_linkAuxiliaryCutoff

end YMGap.Continuum.CanonicalLinkAuxiliarySupportBound
