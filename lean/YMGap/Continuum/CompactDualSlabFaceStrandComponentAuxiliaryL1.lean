/-
# A cutoff-independent local l1 budget for component auxiliary drops

The sparse component code stores natural-valued internal drops.  Bounding each
entry by the source auxiliary cutoff would lose the required cutoff
independence.  The correct invariant is their total `l1` mass.

At one resolved trivalent vertex, the selected output count is at most the sum
of the two selected input counts.  The canonical degree-at-most-six resolver
is a left-associated chain with at most three genuine internal coordinates.
Successive use of the vertex inequality bounds the sum of all internal drops
by three times the sum of the physical input drops.  The degree-one and
degree-two auxiliary coordinates are the forced-zero vacuum terminator and
therefore contribute nothing.

Constructive contract: the existing finite Kirchhoff compiler, literal
degree-zero-through-six cases, and natural arithmetic only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentCodeSize

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2TrivalentStrandPortPairing
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination
open YMGap.Continuum.Z4CanonicalLinkUsedCoordinates
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. A local Kirchhoff inequality at every resolved vertex -/

/-- A mate-closed selection cannot remove more copies from an edge than that
edge carries. -/
theorem ResolvedNetworkMateClosedSelection.drop_le_label
    {label : EdgeLabelling}
    {resolved : List (ResolvedTrivalentVertex label)}
    (selection : ResolvedNetworkMateClosedSelection resolved)
    (edge : Nat) : selection.drop edge <= label edge := by
  unfold ResolvedNetworkMateClosedSelection.drop
  exact boolCountFrom_le _ _ _

/-- At any displayed resolved trivalent vertex, the output drop is at most the
sum of the two input drops. -/
theorem ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    (network : ResolvedTrivalentNetwork vertices label)
    (selection : ResolvedNetworkMateClosedSelection network.resolved)
    (vertex : TrivalentVertex) (hvertex : vertex ∈ vertices) :
    selection.drop vertex.2.2 <=
      selection.drop vertex.1 + selection.drop vertex.2.1 := by
  have hmapped : vertex ∈
      network.resolved.map (fun item => item.vertex) := by
    rw [network.vertices_exact]
    exact hvertex
  obtain ⟨resolved, hresolved, rfl⟩ := List.mem_map.mp hmapped
  let atVertexSelection := selection.atVertex resolved hresolved
  have ha := atVertexSelection.legCount_a
  have hb := atVertexSelection.legCount_b
  have hc := atVertexSelection.legCount_c
  have ha' : selection.drop resolved.vertex.1 =
      atVertexSelection.removal.ca + atVertexSelection.removal.ab := by
    simpa [ResolvedNetworkMateClosedSelection.drop,
      ResolvedNetworkMateClosedSelection.atVertex,
      TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId,
      atVertexSelection] using ha
  have hb' : selection.drop resolved.vertex.2.1 =
      atVertexSelection.removal.bc + atVertexSelection.removal.ab := by
    simpa [ResolvedNetworkMateClosedSelection.drop,
      ResolvedNetworkMateClosedSelection.atVertex,
      TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId,
      atVertexSelection] using hb
  have hc' : selection.drop resolved.vertex.2.2 =
      atVertexSelection.removal.bc + atVertexSelection.removal.ca := by
    simpa [ResolvedNetworkMateClosedSelection.drop,
      ResolvedNetworkMateClosedSelection.atVertex,
      TrivalentMateClosedSelection.legCount, legSize, vertexEdgeId,
      atVertexSelection] using hc
  omega

/-! ## 2. The forced-zero terminator -/

/-- Whenever the canonical vacuum-terminator coordinate is present among the
used auxiliary coordinates, an accepted link guard forces its auxiliary label
to zero. -/
theorem canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hcoordinate : degree ∈ canonicalUsedAuxiliaryCoordinates degree)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true) :
    auxiliary degree = 0 := by
  unfold canonicalLinkConditionalAllowedB at hallowed
  have hparts := (Bool.and_eq_true _ _).mp hallowed
  have hterminator := List.all_eq_true.mp hparts.2 degree hcoordinate
  unfold canonicalAuxiliaryEdgeAllowedB at hterminator
  rw [if_pos rfl] at hterminator
  simp only [decide_eq_true_eq] at hterminator
  unfold overlayOn at hterminator
  have hnot : degree ∉ List.range degree := by
    intro hmem
    exact Nat.lt_irrefl degree (List.mem_range.mp hmem)
  rw [if_neg hnot] at hterminator
  exact hterminator

/-! ## 3. Exhaust the canonical degree-at-most-six chain -/

private theorem canonicalLinkSelection_auxiliary_l1_degree_zero
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 0 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        0 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 0).map selection.drop) <=
      3 * natListSum
        ((List.finRange 0).map fun position =>
          selection.drop position.val) := by
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    natListSum]

private theorem canonicalLinkSelection_auxiliary_l1_degree_one
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 1 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        1 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 1).map selection.drop) <=
      3 * natListSum
        ((List.finRange 1).map fun position =>
          selection.drop position.val) := by
  have hzeroAux : auxiliary 1 = 0 :=
    canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
      (by decide) hallowed
  have hdrop :=
    ResolvedNetworkMateClosedSelection.drop_le_label selection 1
  have hlabel : canonicalLinkLabelling 1 external auxiliary 1 = 0 := by
    unfold canonicalLinkLabelling overlayOn
    simp [hzeroAux]
  rw [hlabel] at hdrop
  change selection.drop 1 <= 3 * selection.drop 0
  omega

private theorem canonicalLinkSelection_auxiliary_l1_degree_two
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 2 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        2 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 2).map selection.drop) <=
      3 * natListSum
        ((List.finRange 2).map fun position =>
          selection.drop position.val) := by
  have hzeroAux : auxiliary 2 = 0 :=
    canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
      (by decide) hallowed
  have hdrop :=
    ResolvedNetworkMateClosedSelection.drop_le_label selection 2
  have hlabel : canonicalLinkLabelling 2 external auxiliary 2 = 0 := by
    unfold canonicalLinkLabelling overlayOn
    simp [hzeroAux]
  rw [hlabel] at hdrop
  change selection.drop 2 <=
    3 * (selection.drop 0 + selection.drop 1)
  omega

private theorem canonicalLinkSelection_auxiliary_l1_degree_three
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 3 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        3 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 3).map selection.drop) <=
      3 * natListSum
        ((List.finRange 3).map fun position =>
          selection.drop position.val) := by
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    natListSum]

private theorem canonicalLinkSelection_auxiliary_l1_degree_four
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 4 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        4 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 4).map selection.drop) <=
      3 * natListSum
        ((List.finRange 4).map fun position =>
          selection.drop position.val) := by
  have hfirst :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 4 external auxiliary hallowed)
      selection
      (0, 1, 5) (by decide)
  simp at hfirst
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    natListSum, List.finRange]
  omega

private theorem canonicalLinkSelection_auxiliary_l1_degree_five
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 5 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        5 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 5).map selection.drop) <=
      3 * natListSum
        ((List.finRange 5).map fun position =>
          selection.drop position.val) := by
  have hfirst :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 5 external auxiliary hallowed)
      selection
      (0, 1, 6) (by decide)
  have hsecond :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 5 external auxiliary hallowed)
      selection
      (6, 2, 7) (by decide)
  simp at hfirst hsecond
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    natListSum, List.finRange]
  omega

private theorem canonicalLinkSelection_auxiliary_l1_degree_six
    {external auxiliary : EdgeLabelling}
    (hallowed :
      canonicalLinkConditionalAllowedB 6 external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        6 external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates 6).map selection.drop) <=
      3 * natListSum
        ((List.finRange 6).map fun position =>
          selection.drop position.val) := by
  have hfirst :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
      selection
      (0, 1, 7) (by decide)
  have hsecond :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
      selection
      (7, 2, 8) (by decide)
  have hthird :=
    ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
      (canonicalLinkResolvedStrandNetwork 6 external auxiliary hallowed)
      selection
      (8, 3, 9) (by decide)
  simp at hfirst hsecond hthird
  have hthree : selection.drop (3 : Fin 6).val =
      selection.drop 3 := by
    rfl
  simp [canonicalUsedAuxiliaryCoordinates, canonicalUsedCoordinates,
    natListSum, List.finRange]
  omega

/-- The sum of all used internal drops of an accepted canonical resolver is at
most three times the sum of its physical input drops.  The constant three is
the maximum number of internal coordinates at degree six and is independent
of every spin label and cutoff. -/
theorem canonicalLinkSelection_auxiliary_l1_le_three_mul_physical_l1
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree <= linkIncidenceBound)
    (hallowed :
      canonicalLinkConditionalAllowedB degree external auxiliary = true)
    (selection : ResolvedNetworkMateClosedSelection
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed).resolved) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates degree).map selection.drop) <=
      3 * natListSum
        ((List.finRange degree).map fun position =>
          selection.drop position.val) := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact canonicalLinkSelection_auxiliary_l1_degree_zero hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_one hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_two hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_three hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_four hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_five hallowed selection
  · exact canonicalLinkSelection_auxiliary_l1_degree_six hallowed selection

/-! ## 4. Literal corrected-slab specialization -/

/-- The generic local budget at a literal corrected-slab link, stated first
on the already-compiled mate-closed selection. -/
theorem SlabLinkPartnerClosedFaceSelection.toMateClosedSelection_auxiliaryDrop_l1_le_three_mul_physicalDrop_l1
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length).map
            selection.toMateClosedSelection.drop) <=
      3 * natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.toMateClosedSelection.drop position.val) :=
  canonicalLinkSelection_auxiliary_l1_le_three_mul_physical_l1
    (degree := (slabIncidentPlaqIds extent link).length)
    (external := slabLinkExternalSpins extent physical link)
    (auxiliary := auxiliary)
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem)
    selection.toMateClosedSelection

/-- One accepted corrected-slab component selection obeys the same local
cutoff-independent `l1` budget. -/
theorem SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_l1_le_three_mul_physicalDrop_l1
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    natListSum
        ((canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length).map selection.drop) <=
      3 * natListSum
        ((List.finRange (slabIncidentPlaqIds extent link).length).map
          fun position => selection.drop position.val) := by
  have hbound :=
    SlabLinkPartnerClosedFaceSelection.toMateClosedSelection_auxiliaryDrop_l1_le_three_mul_physicalDrop_l1
      selection
  rw [SlabLinkPartnerClosedFaceSelection.toMateClosedSelection_drop selection]
    at hbound
  exact hbound

#print axioms ResolvedNetworkMateClosedSelection.drop_le_label
#print axioms ResolvedNetworkMateClosedSelection.drop_third_le_first_add_second
#print axioms canonicalLinkConditionalAllowedB_auxiliary_degree_eq_zero
#print axioms canonicalLinkSelection_auxiliary_l1_le_three_mul_physical_l1
#print axioms SlabLinkPartnerClosedFaceSelection.toMateClosedSelection_auxiliaryDrop_l1_le_three_mul_physicalDrop_l1
#print axioms SlabLinkPartnerClosedFaceSelection.auxiliaryDrop_l1_le_three_mul_physicalDrop_l1

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryL1
