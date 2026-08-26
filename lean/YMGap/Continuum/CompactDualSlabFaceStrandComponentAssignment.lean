/-
# A rooted face-strand component constructs one accepted global assignment

The component-drop theorem produces, at every displayed lattice link, an
accepted lowered auxiliary labelling for one common lowered physical
labelling.  This module performs the remaining Cartesian assembly.

The mathematical content is deliberately small.  Mapping any link-indexed
family of locally accepted auxiliaries over a link list gives a member of the
recursive Cartesian assignment list.  Applying that lemma to the component's
explicit local peel yields a single accepted global target assignment, and
lookup recovers its prescribed local value exactly.

Constructive contract: structural recursion on the literal link list and one
decidable membership split for totalizing the local field.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## 1. Cartesian assembly from a local accepted field -/

/-- Write a link-indexed auxiliary field in the literal order of a link list. -/
def slabFusionWitnessAssignmentFrom
    (links : List SlabLink)
    (auxiliaryAt : SlabLink -> SlabLabelling) :
    SlabFusionWitnessAssignment :=
  links.map fun link => (link, auxiliaryAt link)

/-- Structural Cartesian assembly: local acceptedness at every displayed link
is exactly the data needed to construct a member of the global assignment
list. -/
theorem slabFusionWitnessAssignmentFrom_mem
    (K extent : Nat) (physical : SlabLabelling)
    (auxiliaryAt : SlabLink -> SlabLabelling) :
    forall links : List SlabLink,
      (forall link, link ∈ links ->
        auxiliaryAt link ∈
          slabLinkFusionWitnesses K extent physical link) ->
      slabFusionWitnessAssignmentFrom links auxiliaryAt ∈
        slabFusionWitnessAssignmentsOn K extent physical links
  | [], _ => by
      simp [slabFusionWitnessAssignmentFrom,
        slabFusionWitnessAssignmentsOn]
  | head :: rest, hlocal => by
      unfold slabFusionWitnessAssignmentFrom
      simp only [List.map_cons, slabFusionWitnessAssignmentsOn]
      apply List.mem_flatMap.mpr
      refine ⟨auxiliaryAt head, hlocal head (by simp), ?_⟩
      apply List.mem_map.mpr
      refine ⟨slabFusionWitnessAssignmentFrom rest auxiliaryAt, ?_, rfl⟩
      exact slabFusionWitnessAssignmentFrom_mem
        K extent physical auxiliaryAt rest fun link hlink =>
          hlocal link (List.mem_cons_of_mem head hlink)

/-- Lookup in an assembled field returns the prescribed local auxiliary at
every displayed link, including when the link list contains duplicates. -/
theorem slabFusionWitnessAssignmentAt_from
    (auxiliaryAt : SlabLink -> SlabLabelling) :
    forall (links : List SlabLink) (link : SlabLink),
      link ∈ links ->
      slabFusionWitnessAssignmentAt link
          (slabFusionWitnessAssignmentFrom links auxiliaryAt) =
        auxiliaryAt link
  | [], link, hlink => False.elim (List.not_mem_nil hlink)
  | head :: rest, link, hlink => by
      by_cases hsame : head = link
      · subst link
        simp [slabFusionWitnessAssignmentFrom,
          slabFusionWitnessAssignmentAt]
      · have hrest : link ∈ rest := by
          rcases List.mem_cons.mp hlink with hhead | htail
          · exact False.elim (hsame hhead.symm)
          · exact htail
        simp only [slabFusionWitnessAssignmentFrom, List.map_cons,
          slabFusionWitnessAssignmentAt, hsame, if_false]
        exact slabFusionWitnessAssignmentAt_from auxiliaryAt rest link hrest

/-! ## 2. The globally accepted component peel -/

/-- Totalize the component's explicit lowered auxiliary field outside the
displayed link list.  The default branch is absent from the assembled list. -/
def SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) : SlabLabelling :=
  if hlink : link ∈ links then
    lowerEdgeLabellingBy
      (slabFusionWitnessAssignmentAt link assignment)
      (seed.atLinkSelection ⟨link, hlink⟩).drop
  else zeroEdgeLabelling

/-- On a displayed link the total field is the literal component lowering. -/
@[simp] theorem SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt_of_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt seed link =
      lowerEdgeLabellingBy
        (slabFusionWitnessAssignmentAt link assignment)
        (seed.atLinkSelection ⟨link, hlink⟩).drop := by
  simp [SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt, hlink]

/-- The component's canonical globally lowered fusion assignment. -/
def SlabFusionWitnessFaceStrandSeed.lowerAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom links
    (SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt seed)

/-- **Global accepted component peel.**  One rooted strand component produces
one actual member of the complete target Cartesian fusion-assignment list. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerAssignment_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    SlabFusionWitnessFaceStrandSeed.lowerAssignment seed ∈
      slabFusionWitnessAssignmentsOn K extent
        (SlabFusionWitnessFaceStrandSeed.lowerPhysical seed) links := by
  apply slabFusionWitnessAssignmentFrom_mem
  intro link hlink
  rw [SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt_of_mem
    seed link hlink]
  exact SlabFusionWitnessFaceStrandSeed.lower_auxiliary_mem_atLink
    seed ⟨link, hlink⟩

/-- Lookup in the globally lowered assignment returns exactly the local
component lowering used to prove acceptedness. -/
theorem SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    slabFusionWitnessAssignmentAt link
        (SlabFusionWitnessFaceStrandSeed.lowerAssignment seed) =
      lowerEdgeLabellingBy
        (slabFusionWitnessAssignmentAt link assignment)
        (seed.atLinkSelection ⟨link, hlink⟩).drop := by
  unfold SlabFusionWitnessFaceStrandSeed.lowerAssignment
  rw [slabFusionWitnessAssignmentAt_from
    (SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt seed)
    links link hlink]
  exact SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt_of_mem
    seed link hlink

#print axioms slabFusionWitnessAssignmentFrom
#print axioms slabFusionWitnessAssignmentFrom_mem
#print axioms slabFusionWitnessAssignmentAt_from
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAuxiliaryAt_of_mem
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAssignment
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAssignment_mem
#print axioms SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
