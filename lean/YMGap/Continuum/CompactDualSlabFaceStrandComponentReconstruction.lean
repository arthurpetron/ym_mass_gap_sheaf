/-
# Exact reconstruction after an accepted rooted component peel

The component-payment theorem supplies the energy half of a Peierls map.  Its
inverse-counting half must first establish that the removed data really codes
the source.  This module proves that algebraic left inverse.

For physical faces, re-add the exact selected-copy count pointwise.  For a
link auxiliary witness, re-add the component drop only on the canonical
auxiliary-coordinate support.  The mask is essential: the same strand drop
also has physical-edge coordinates, while an auxiliary labelling vanishes
there.  Accepted source membership supplies both support and the bound needed
for natural subtraction cancellation.

The final specialization reconstructs the entire source assignment on the
duplicate-free complete slab-link list.  Thus the remaining inverse code is
purely geometric: it must describe the rooted strand component/drop profile,
not store any additional source spin or fusion labels.

Constructive contract: pointwise natural subtraction/addition, explicit
finite support masks, and structural recursion on the literal assignment
list.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition
open YMGap.Continuum.Z4ConditionalLinkAuxiliaryElimination

/-! ## 1. Pointwise left inverses for bounded natural subtraction -/

/-- Re-add one natural edge-drop labelling pointwise. -/
def raiseEdgeLabellingBy
    (label drop : EdgeLabelling) : EdgeLabelling :=
  fun edge => label edge + drop edge

/-- Pointwise bounded subtraction followed by re-addition is exact. -/
theorem raiseEdgeLabellingBy_lowerEdgeLabellingBy
    (label drop : EdgeLabelling)
    (hdrop : forall edge, drop edge <= label edge) :
    raiseEdgeLabellingBy (lowerEdgeLabellingBy label drop) drop = label := by
  funext edge
  unfold raiseEdgeLabellingBy lowerEdgeLabellingBy
  exact Nat.sub_add_cancel (hdrop edge)

/-- Retain a drop only on an explicit finite edge support. -/
def edgeLabellingSupportedOn
    (edges : List Nat) (drop : EdgeLabelling) : EdgeLabelling :=
  fun edge => if edge ∈ edges then drop edge else 0

/-- If the source vanishes off a support and the drop is bounded on it, the
support-masked drop reconstructs the source from the globally lowered label. -/
theorem raiseEdgeLabellingBy_lowerEdgeLabellingBy_supported
    (edges : List Nat) (label drop : EdgeLabelling)
    (hsupport : forall edge, edge ∉ edges -> label edge = 0)
    (hdrop : forall edge, edge ∈ edges -> drop edge <= label edge) :
    raiseEdgeLabellingBy
        (lowerEdgeLabellingBy label drop)
        (edgeLabellingSupportedOn edges drop) = label := by
  funext edge
  by_cases hedge : edge ∈ edges
  · unfold raiseEdgeLabellingBy lowerEdgeLabellingBy
      edgeLabellingSupportedOn
    rw [if_pos hedge, Nat.sub_add_cancel (hdrop edge hedge)]
  · unfold raiseEdgeLabellingBy lowerEdgeLabellingBy
      edgeLabellingSupportedOn
    rw [if_neg hedge, hsupport edge hedge]
    simp only [Nat.zero_sub, Nat.zero_add]

/-! ## 2. Exact physical-label reconstruction -/

/-- The physical part of the rooted-component inverse code. -/
def SlabFusionWitnessFaceStrandSeed.physicalDrop
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : SlabLabelling :=
  slabFaceStrandSelectionCount seed.selected

/-- Reconstruct physical labels by adding the component incidence profile to
the accepted lowered target. -/
def SlabFusionWitnessFaceStrandSeed.reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) : SlabLabelling :=
  raiseEdgeLabellingBy
    (YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical seed)
    (SlabFusionWitnessFaceStrandSeed.physicalDrop seed)

/-- The lowered physical target plus its component drop is exactly the source
physical labelling. -/
theorem SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    SlabFusionWitnessFaceStrandSeed.reconstructPhysical seed = physical := by
  unfold SlabFusionWitnessFaceStrandSeed.reconstructPhysical
    SlabFusionWitnessFaceStrandSeed.physicalDrop
    YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical
    lowerSlabPhysicalByFaceStrandSelection
  apply raiseEdgeLabellingBy_lowerEdgeLabellingBy
  exact slabFaceStrandSelectionCount_le seed.selected

/-! ## 3. Exact supported auxiliary-label reconstruction -/

/-- A compiled component drop never exceeds the source canonical link label. -/
theorem SlabLinkPartnerClosedFaceSelection.drop_le_canonical
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (edge : Nat) :
    selection.drop edge <=
      canonicalLinkLabelling
        (slabIncidentPlaqIds extent link).length
        (slabLinkExternalSpins extent physical link) auxiliary edge := by
  unfold SlabLinkPartnerClosedFaceSelection.drop
  exact boolCountFrom_le _ _ _

/-- On a canonical auxiliary coordinate, the compiled component drop is
bounded by the source auxiliary label itself. -/
theorem SlabLinkPartnerClosedFaceSelection.drop_le_auxiliary
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (edge : Nat)
    (hedge : edge ∈ canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length) :
    selection.drop edge <= auxiliary edge := by
  have hdegree :
      (slabIncidentPlaqIds extent link).length <= linkIncidenceBound :=
    slabIncidentPlaqIds_length_le_six extent link
  obtain ⟨offset, hedgeEq, _⟩ :=
    canonicalUsedAuxiliary_coordinate_shape hdegree hedge
  have hnotPhysical :
      edge ∉ List.range (slabIncidentPlaqIds extent link).length := by
    intro hmemRange
    have hlt := List.mem_range.mp hmemRange
    omega
  have hbound :=
    SlabLinkPartnerClosedFaceSelection.drop_le_canonical selection edge
  unfold canonicalLinkLabelling overlayOn at hbound
  rw [if_neg hnotPhysical] at hbound
  exact hbound

/-- Re-add precisely the internal-coordinate part of a component drop. -/
def SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (target : SlabLabelling) : SlabLabelling :=
  raiseEdgeLabellingBy target
    (edgeLabellingSupportedOn
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      selection.drop)

/-- The accepted lowered auxiliary target plus the supported component drop
is exactly the source auxiliary witness. -/
theorem SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :
    SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary selection
        (lowerEdgeLabellingBy auxiliary selection.drop) = auxiliary := by
  apply raiseEdgeLabellingBy_lowerEdgeLabellingBy_supported
  · have hbounded : auxiliary ∈
        boundedEdgeLabellings (linkAuxiliaryCutoff cutoff)
          (canonicalUsedAuxiliaryCoordinates
            (slabIncidentPlaqIds extent link).length) :=
      (List.mem_filter.mp hmem).1
    exact (boundedEdgeLabellings_sound
      (linkAuxiliaryCutoff cutoff)
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length)
      auxiliary hbounded).2
  · exact SlabLinkPartnerClosedFaceSelection.drop_le_auxiliary selection

/-! ## 4. Exact global-assignment reconstruction -/

/-- On a duplicate-free link list, the field of assignment lookups writes the
original Cartesian assignment back in its literal order. -/
theorem slabFusionWitnessAssignmentFrom_at_eq
    (K extent : Nat) (physical : SlabLabelling) :
    forall (links : List SlabLink)
      (assignment : SlabFusionWitnessAssignment),
      links.Nodup ->
      assignment ∈
        slabFusionWitnessAssignmentsOn K extent physical links ->
      slabFusionWitnessAssignmentFrom links
          (fun link => slabFusionWitnessAssignmentAt link assignment) =
        assignment
  | [], assignment, _, hassignment => by
      simp only [slabFusionWitnessAssignmentsOn, List.mem_singleton]
        at hassignment
      subst assignment
      rfl
  | head :: rest, assignment, hnodup, hassignment => by
      obtain ⟨selected, _, hselectedBlock⟩ :=
        List.mem_flatMap.mp hassignment
      obtain ⟨tail, htail, rfl⟩ := List.mem_map.mp hselectedBlock
      have hparts := List.nodup_cons.mp hnodup
      have ih := slabFusionWitnessAssignmentFrom_at_eq
        K extent physical rest tail hparts.2 htail
      unfold slabFusionWitnessAssignmentFrom
      simp only [List.map_cons]
      congr 1
      · simp [slabFusionWitnessAssignmentAt]
      · calc
          rest.map (fun link =>
              (link, slabFusionWitnessAssignmentAt link
                ((head, selected) :: tail))) =
              rest.map (fun link =>
                (link, slabFusionWitnessAssignmentAt link tail)) := by
            apply List.map_congr_left
            intro link hlink
            have hne : head ≠ link := by
              intro heq
              apply hparts.1
              rw [heq]
              exact hlink
            simp [slabFusionWitnessAssignmentAt, hne]
          _ = tail := ih

/-- Reconstruct the source auxiliary carried by one displayed link from the
globally lowered assignment and the rooted component's internal drop. -/
def SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) : SlabLabelling :=
  SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary
    (YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent.SlabFusionWitnessFaceStrandSeed.atLinkSelection
      seed ⟨link, hlink⟩)
    (slabFusionWitnessAssignmentAt link
      (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
        seed))

/-- Linkwise reconstruction returns the literal source auxiliary lookup. -/
theorem SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt_eq
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt
        seed link hlink =
      slabFusionWitnessAssignmentAt link assignment := by
  unfold SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt
  rw [YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink
    seed link hlink]
  exact
    SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
      (YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent.SlabFusionWitnessFaceStrandSeed.atLinkSelection
        seed ⟨link, hlink⟩)

/-- Totalize the reconstructed source auxiliary field outside the displayed
link list.  As before, the default branch is absent from the assembled list. -/
def SlabFusionWitnessFaceStrandSeed.reconstructedAuxiliaryField
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) : SlabLabelling :=
  if hlink : link ∈ links then
    SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt seed link hlink
  else zeroEdgeLabelling

/-- Assemble the full reconstructed source assignment in the original link
order. -/
def SlabFusionWitnessFaceStrandSeed.reconstructAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom links
    (SlabFusionWitnessFaceStrandSeed.reconstructedAuxiliaryField seed)

/-- **Global algebraic left inverse.**  On any duplicate-free displayed link
list, the accepted lowered target plus the rooted component drops reconstruct
the entire literal source fusion assignment. -/
theorem SlabFusionWitnessFaceStrandSeed.reconstructAssignment_eq
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    SlabFusionWitnessFaceStrandSeed.reconstructAssignment seed =
      assignment := by
  calc
    SlabFusionWitnessFaceStrandSeed.reconstructAssignment seed =
        slabFusionWitnessAssignmentFrom links
          (fun link => slabFusionWitnessAssignmentAt link assignment) := by
      unfold SlabFusionWitnessFaceStrandSeed.reconstructAssignment
        slabFusionWitnessAssignmentFrom
      apply List.map_congr_left
      intro link hlink
      unfold SlabFusionWitnessFaceStrandSeed.reconstructedAuxiliaryField
      rw [dif_pos hlink]
      congr 1
      exact SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt_eq
        seed link hlink
    _ = assignment := slabFusionWitnessAssignmentFrom_at_eq
      K extent physical links assignment hnodup hassignment

/-- The production complete slab link carrier is duplicate-free, so every
rooted peel there has an unconditional whole-assignment left inverse. -/
theorem SlabFusionWitnessFaceStrandSeed.reconstructCompleteAssignment_eq
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    SlabFusionWitnessFaceStrandSeed.reconstructAssignment seed =
      assignment :=
  SlabFusionWitnessFaceStrandSeed.reconstructAssignment_eq seed
    (boundaryCompleteSlabLinks_nodup extent)

#print axioms raiseEdgeLabellingBy
#print axioms raiseEdgeLabellingBy_lowerEdgeLabellingBy
#print axioms edgeLabellingSupportedOn
#print axioms raiseEdgeLabellingBy_lowerEdgeLabellingBy_supported
#print axioms SlabFusionWitnessFaceStrandSeed.physicalDrop
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq
#print axioms SlabLinkPartnerClosedFaceSelection.drop_le_canonical
#print axioms SlabLinkPartnerClosedFaceSelection.drop_le_auxiliary
#print axioms SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary
#print axioms SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
#print axioms slabFusionWitnessAssignmentFrom_at_eq
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructAuxiliaryAt_eq
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructedAuxiliaryField
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructAssignment
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructAssignment_eq
#print axioms SlabFusionWitnessFaceStrandSeed.reconstructCompleteAssignment_eq

end YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
