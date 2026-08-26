/-
# Finite drop codes for accepted rooted strand-component peels

The preceding reconstruction theorem still reads the rooted component seed
directly.  That is an algebraic left inverse, but not yet an inverse-counting
argument.  This module factors every value read by reconstruction through a
plain finite code:

* a sparse list of physical face identifiers, repeated with the removed
  multiplicity; and
* one finite word of canonical auxiliary-coordinate drops for every displayed
  slab link.

The decoder uses only the lowered target, the fixed geometry, and this code.
Encoding a seed and decoding its accepted target reconstructs the literal
source physical labelling and source global fusion assignment.  Each local
auxiliary word has length at most three, independently of the spin cutoff.

This is the serialization and left-inverse layer only.  The auxiliary table is
still indexed by the whole displayed link list; sparsifying it to component
support and proving a cutoff- and volume-independent exponential code count
remain separate obligations.

Constructive contract: finite lists, recursive lookups, and exact natural
arithmetic only.  No `Classical.*`, choice, `native_decide`, `sorry`, custom
axiom, noncomputable declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
import YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.ResolvedTrivalentNetworkStrandRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Exact finite-word decoding on a duplicate-free support -/

/-- Decoding the values of a labelling along a duplicate-free finite support
returns exactly its zero extension from that support. -/
theorem wordToEdgeLabelling_map_eq_supportedOn
    (label : EdgeLabelling) : forall edges : List Nat,
    edges.Nodup ->
    wordToEdgeLabelling edges (edges.map label) =
      edgeLabellingSupportedOn edges label
  | [], _ => by
      funext edge
      simp [wordToEdgeLabelling, edgeLabellingSupportedOn,
        zeroEdgeLabelling]
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      funext edge
      by_cases heq : edge = head
      · subst edge
        simp [wordToEdgeLabelling, edgeLabellingSupportedOn, setEdgeLabel]
      · simp only [List.map_cons, wordToEdgeLabelling]
        rw [show setEdgeLabel
              (wordToEdgeLabelling tail (tail.map label))
                head (label head) edge =
              wordToEdgeLabelling tail (tail.map label) edge by
            simp [setEdgeLabel, heq]]
        rw [wordToEdgeLabelling_map_eq_supportedOn label tail hparts.2]
        unfold edgeLabellingSupportedOn
        simp [heq]

/-! ## 2. A finite source-independent drop-code format -/

/-- The finite information consumed by component reconstruction.  Physical
drops are stored sparsely as repeated face identifiers.  Auxiliary drops are
fixed-order words attached to displayed links. -/
structure SlabFaceStrandComponentDropCode where
  physicalFaces : List Nat
  auxiliaryWords : List (SlabLink × List Nat)

/-- Write a link-indexed word field in the literal order of a link list. -/
def slabAuxiliaryDropWordsFrom
    (links : List SlabLink) (wordAt : SlabLink -> List Nat) :
    List (SlabLink × List Nat) :=
  links.map fun link => (link, wordAt link)

/-- Total lookup of a link word, with the empty word as the irrelevant
off-carrier default. -/
def slabAuxiliaryDropWordAt (link : SlabLink) :
    List (SlabLink × List Nat) -> List Nat
  | [] => []
  | entry :: rest =>
      if entry.1 = link then entry.2
      else slabAuxiliaryDropWordAt link rest

/-- Lookup in a fixed-order word field returns its prescribed value at every
displayed link, including for lists with duplicate links. -/
theorem slabAuxiliaryDropWordAt_from
    (wordAt : SlabLink -> List Nat) :
    forall (links : List SlabLink) (link : SlabLink),
      link ∈ links ->
      slabAuxiliaryDropWordAt link
          (slabAuxiliaryDropWordsFrom links wordAt) = wordAt link
  | [], link, hlink => False.elim (List.not_mem_nil hlink)
  | head :: rest, link, hlink => by
      by_cases hsame : head = link
      · subst link
        simp [slabAuxiliaryDropWordsFrom, slabAuxiliaryDropWordAt]
      · have hrest : link ∈ rest := by
          rcases List.mem_cons.mp hlink with hhead | htail
          · exact False.elim (hsame hhead.symm)
          · exact htail
        simp only [slabAuxiliaryDropWordsFrom, List.map_cons,
          slabAuxiliaryDropWordAt, hsame, if_false]
        exact slabAuxiliaryDropWordAt_from wordAt rest link hrest

/-- Decode the sparse physical multiplicity list as a pointwise drop. -/
def SlabFaceStrandComponentDropCode.decodePhysicalDrop
    (code : SlabFaceStrandComponentDropCode) : SlabLabelling :=
  fun faceId => code.physicalFaces.count faceId

/-- Decode one link's fixed-order internal-coordinate word as an edge
labelling supported on that link's canonical auxiliary coordinates. -/
def SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
    (code : SlabFaceStrandComponentDropCode)
    (extent : Nat) (link : SlabLink) : SlabLabelling :=
  wordToEdgeLabelling
    (canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length)
    (slabAuxiliaryDropWordAt link code.auxiliaryWords)

/-! ## 3. Encode exactly the values read from a rooted component -/

/-- The canonical internal-drop word at one displayed link. -/
def SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) : List Nat :=
  if hlink : link ∈ links then
    (canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent link).length).map
        (seed.atLinkSelection ⟨link, hlink⟩).drop
  else []

/-- On a displayed link the totalized word is the literal internal drop. -/
@[simp] theorem SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link =
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent link).length).map
          (seed.atLinkSelection ⟨link, hlink⟩).drop := by
  simp [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt, hlink]

/-- Serialize one rooted component without retaining the seed object. -/
def SlabFusionWitnessFaceStrandSeed.dropCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    SlabFaceStrandComponentDropCode where
  physicalFaces :=
    YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight.SlabFusionWitnessFaceStrandSeed.peelFaces
      seed
  auxiliaryWords := slabAuxiliaryDropWordsFrom links
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)

/-- The encoded physical word decodes to the exact selected-copy count. -/
theorem SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_dropCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).decodePhysicalDrop =
      SlabFusionWitnessFaceStrandSeed.physicalDrop seed := by
  funext faceId
  unfold SlabFaceStrandComponentDropCode.decodePhysicalDrop
    SlabFusionWitnessFaceStrandSeed.dropCode
    SlabFusionWitnessFaceStrandSeed.physicalDrop
  exact SlabFusionWitnessFaceStrandSeed.peelFaces_count seed faceId

/-- The encoded word at a displayed link decodes to precisely the supported
internal part of the component drop used by the algebraic inverse. -/
theorem SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_dropCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).decodeAuxiliaryDrop
        extent link =
      edgeLabellingSupportedOn
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length)
        (seed.atLinkSelection ⟨link, hlink⟩).drop := by
  let coordinates := canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds extent link).length
  have hlookup :
      slabAuxiliaryDropWordAt link
          (SlabFusionWitnessFaceStrandSeed.dropCode seed).auxiliaryWords =
        SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link := by
    unfold SlabFusionWitnessFaceStrandSeed.dropCode
    exact slabAuxiliaryDropWordAt_from
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
      links link hlink
  have hdegree :
      (slabIncidentPlaqIds extent link).length <= linkIncidenceBound :=
    slabIncidentPlaqIds_length_le_six extent link
  unfold SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
  rw [hlookup,
    SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
      seed link hlink]
  exact wordToEdgeLabelling_map_eq_supportedOn
    (seed.atLinkSelection ⟨link, hlink⟩).drop
    coordinates
    (canonicalUsedAuxiliaryCoordinates_nodup hdegree)

/-! ## 4. Cutoff-independent local code shape -/

/-- A degree-at-most-six resolver has at most three used auxiliary
coordinates. -/
theorem canonicalUsedAuxiliaryCoordinates_length_le_three
    {degree : Nat} (hdegree : degree <= linkIncidenceBound) :
    (canonicalUsedAuxiliaryCoordinates degree).length <= 3 := by
  unfold linkIncidenceBound at hdegree
  have hd : degree = 0 ∨ degree = 1 ∨ degree = 2 ∨ degree = 3 ∨
      degree = 4 ∨ degree = 5 ∨ degree = 6 := by
    omega
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- Every encoded displayed-link word has length at most three, with no
dependence on the spin cutoff. -/
theorem SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_length_le_three
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) :
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link).length <=
      3 := by
  by_cases hlink : link ∈ links
  · rw [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
      seed link hlink, List.length_map]
    exact canonicalUsedAuxiliaryCoordinates_length_le_three
      (slabIncidentPlaqIds_length_le_six extent link)
  · simp [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt, hlink]

/-- The auxiliary table has exactly one row per displayed link. -/
theorem SlabFusionWitnessFaceStrandSeed.dropCode_auxiliaryWords_length
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).auxiliaryWords.length =
      links.length := by
  unfold SlabFusionWitnessFaceStrandSeed.dropCode
    slabAuxiliaryDropWordsFrom
  exact List.length_map _

/-! ## 5. Reconstruction reads only the lowered target and the finite code -/

/-- Reconstruct a physical source candidate from a lowered target and code. -/
def SlabFaceStrandComponentDropCode.reconstructPhysical
    (code : SlabFaceStrandComponentDropCode)
    (target : SlabLabelling) : SlabLabelling :=
  raiseEdgeLabellingBy target code.decodePhysicalDrop

/-- Reconstruct one auxiliary source candidate from a lowered assignment and
the link word in the code. -/
def SlabFaceStrandComponentDropCode.reconstructAuxiliaryAt
    (code : SlabFaceStrandComponentDropCode)
    (extent : Nat) (targetAssignment : SlabFusionWitnessAssignment)
    (link : SlabLink) : SlabLabelling :=
  raiseEdgeLabellingBy
    (slabFusionWitnessAssignmentAt link targetAssignment)
    (code.decodeAuxiliaryDrop extent link)

/-- Totalize code-based auxiliary reconstruction outside a displayed link
list. -/
def SlabFaceStrandComponentDropCode.reconstructedAuxiliaryField
    (code : SlabFaceStrandComponentDropCode)
    (extent : Nat) (links : List SlabLink)
    (targetAssignment : SlabFusionWitnessAssignment)
    (link : SlabLink) : SlabLabelling :=
  if link ∈ links then
    code.reconstructAuxiliaryAt extent targetAssignment link
  else zeroEdgeLabelling

/-- Assemble the complete code-reconstructed source assignment. -/
def SlabFaceStrandComponentDropCode.reconstructAssignment
    (code : SlabFaceStrandComponentDropCode)
    (extent : Nat) (links : List SlabLink)
    (targetAssignment : SlabFusionWitnessAssignment) :
    SlabFusionWitnessAssignment :=
  slabFusionWitnessAssignmentFrom links
    (code.reconstructedAuxiliaryField extent links targetAssignment)

/-- Decoding an encoded seed against its accepted lowered physical target
recovers the literal source physical labelling. -/
theorem SlabFusionWitnessFaceStrandSeed.dropCode_reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).reconstructPhysical
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical
          seed) = physical := by
  unfold SlabFaceStrandComponentDropCode.reconstructPhysical
  rw [SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_dropCode seed]
  exact SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq seed

/-- At each displayed link, code decoding against the accepted lowered
assignment recovers the literal source auxiliary lookup. -/
theorem SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (link : SlabLink) (hlink : link ∈ links) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).reconstructAuxiliaryAt
        extent
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed)
        link =
      slabFusionWitnessAssignmentAt link assignment := by
  unfold SlabFaceStrandComponentDropCode.reconstructAuxiliaryAt
  rw [YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink
    seed link hlink]
  rw [SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_dropCode
    seed link hlink]
  exact
    SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
      (seed.atLinkSelection ⟨link, hlink⟩)

/-- **Finite-code global left inverse.**  On a duplicate-free displayed link
list, the encoded finite drop code and accepted lowered target reconstruct the
literal source fusion assignment without retaining the seed. -/
theorem SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).reconstructAssignment
        extent links
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed) = assignment := by
  calc
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).reconstructAssignment
          extent links
          (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
            seed) =
        slabFusionWitnessAssignmentFrom links
          (fun link => slabFusionWitnessAssignmentAt link assignment) := by
      unfold SlabFaceStrandComponentDropCode.reconstructAssignment
        slabFusionWitnessAssignmentFrom
      apply List.map_congr_left
      intro link hlink
      congr 1
      unfold SlabFaceStrandComponentDropCode.reconstructedAuxiliaryField
      rw [if_pos hlink]
      exact SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAuxiliaryAt
        seed link hlink
    _ = assignment := slabFusionWitnessAssignmentFrom_at_eq
      K extent physical links assignment hnodup hassignment

/-- The production complete slab-link carrier supplies the duplicate-free
hypothesis to the finite-code global left inverse. -/
theorem SlabFusionWitnessFaceStrandSeed.dropCode_reconstructCompleteAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.dropCode seed).reconstructAssignment
        extent (boundaryCompleteSlabLinks extent)
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed) = assignment :=
  SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAssignment seed
    (boundaryCompleteSlabLinks_nodup extent)

#print axioms wordToEdgeLabelling_map_eq_supportedOn
#print axioms SlabFaceStrandComponentDropCode
#print axioms slabAuxiliaryDropWordsFrom
#print axioms slabAuxiliaryDropWordAt
#print axioms slabAuxiliaryDropWordAt_from
#print axioms SlabFaceStrandComponentDropCode.decodePhysicalDrop
#print axioms SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
#print axioms SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode
#print axioms SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_dropCode
#print axioms SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_dropCode
#print axioms canonicalUsedAuxiliaryCoordinates_length_le_three
#print axioms SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_length_le_three
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode_auxiliaryWords_length
#print axioms SlabFaceStrandComponentDropCode.reconstructPhysical
#print axioms SlabFaceStrandComponentDropCode.reconstructAuxiliaryAt
#print axioms SlabFaceStrandComponentDropCode.reconstructedAuxiliaryField
#print axioms SlabFaceStrandComponentDropCode.reconstructAssignment
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode_reconstructPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAuxiliaryAt
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode_reconstructAssignment
#print axioms SlabFusionWitnessFaceStrandSeed.dropCode_reconstructCompleteAssignment

end YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
