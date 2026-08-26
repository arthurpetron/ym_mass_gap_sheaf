/-
# Sparse auxiliary drop codes for rooted strand-component peels

The first finite drop code carries one auxiliary word for every displayed
volume link.  This module performs the next exact contraction: rows whose word
is identically zero are omitted.  A structural lookup theorem proves that
decoding the sparse table gives exactly the same edge labelling as decoding
the full table.  Consequently the sparse code retains the whole-configuration
left inverse.

Every retained row is certified nonzero and the sparse table has no more rows
than the displayed link list.  The remaining load-bearing entropy theorem is
geometric: inject or charge retained rows to selected physical component
incidences, giving a bound proportional to component size rather than volume.

Constructive contract: Boolean recursion and finite list lookup only.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, noncomputable
declaration, or enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.FiniteBoundedEdgeLabellingVariableElimination
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Executable zero-word recognition -/

/-- Boolean recognition of finite words all of whose entries are zero. -/
def finiteWordAllZeroB : List Nat -> Bool
  | [] => true
  | value :: values => decide (value = 0) && finiteWordAllZeroB values

/-- An all-zero word decodes to the zero edge labelling for every coordinate
list, including mismatch branches of the total decoder. -/
theorem wordToEdgeLabelling_eq_zero_of_finiteWordAllZeroB :
    forall (coordinates word : List Nat), finiteWordAllZeroB word = true ->
      wordToEdgeLabelling coordinates word = zeroEdgeLabelling
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | coordinate :: coordinates, value :: values, hzero => by
      change
        (decide (value = 0) && finiteWordAllZeroB values) = true at hzero
      have hparts :
          decide (value = 0) = true ∧ finiteWordAllZeroB values = true := by
        simpa only [Bool.and_eq_true] using hzero
      have hvalue : value = 0 := of_decide_eq_true hparts.1
      have htail := wordToEdgeLabelling_eq_zero_of_finiteWordAllZeroB
        coordinates values hparts.2
      rw [hvalue, wordToEdgeLabelling, htail]
      funext edge
      simp [setEdgeLabel, zeroEdgeLabelling]

/-! ## 2. Erase zero rows and preserve decoded lookup -/

/-- Omit every identically-zero link word from a fixed-order word field. -/
def slabSparseAuxiliaryDropWordsFrom :
    List SlabLink -> (SlabLink -> List Nat) ->
      List (SlabLink × List Nat)
  | [], _ => []
  | link :: links, wordAt =>
      if finiteWordAllZeroB (wordAt link) then
        slabSparseAuxiliaryDropWordsFrom links wordAt
      else
        (link, wordAt link) ::
          slabSparseAuxiliaryDropWordsFrom links wordAt

/-- A key absent from the displayed link carrier is also absent from its
sparse word table. -/
theorem slabAuxiliaryDropWordAt_sparseFrom_of_not_mem
    (wordAt : SlabLink -> List Nat) :
    forall (links : List SlabLink) (link : SlabLink),
      link ∉ links ->
      slabAuxiliaryDropWordAt link
          (slabSparseAuxiliaryDropWordsFrom links wordAt) = []
  | [], _, _ => rfl
  | head :: tail, link, hnot => by
      have hne : head ≠ link := by
        intro heq
        apply hnot
        rw [heq]
        exact List.mem_cons_self
      have htail : link ∉ tail := by
        intro hmem
        exact hnot (List.mem_cons_of_mem head hmem)
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte, slabAuxiliaryDropWordAt,
            hne]
          exact slabAuxiliaryDropWordAt_sparseFrom_of_not_mem
            wordAt tail link htail
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            ↓reduceIte]
          exact slabAuxiliaryDropWordAt_sparseFrom_of_not_mem
            wordAt tail link htail

/-- Sparse lookup and full lookup have exactly the same decoded edge
labelling on a duplicate-free displayed link carrier. -/
theorem wordToEdgeLabelling_sparseAuxiliaryDropWordsFrom
    (coordinatesAt : SlabLink -> List Nat)
    (wordAt : SlabLink -> List Nat) :
    forall (links : List SlabLink) (link : SlabLink),
      links.Nodup -> link ∈ links ->
      wordToEdgeLabelling (coordinatesAt link)
          (slabAuxiliaryDropWordAt link
            (slabSparseAuxiliaryDropWordsFrom links wordAt)) =
        wordToEdgeLabelling (coordinatesAt link) (wordAt link)
  | [], link, _, hlink => False.elim (List.not_mem_nil hlink)
  | head :: tail, link, hnodup, hlink => by
      have hparts := List.nodup_cons.mp hnodup
      by_cases hsame : head = link
      · subst link
        cases hzero : finiteWordAllZeroB (wordAt head) with
        | false =>
            simp [slabSparseAuxiliaryDropWordsFrom, hzero,
              slabAuxiliaryDropWordAt]
        | true =>
            have hlookup :=
              slabAuxiliaryDropWordAt_sparseFrom_of_not_mem
                wordAt tail head hparts.1
            rw [show slabSparseAuxiliaryDropWordsFrom (head :: tail) wordAt =
                slabSparseAuxiliaryDropWordsFrom tail wordAt by
              simp [slabSparseAuxiliaryDropWordsFrom, hzero]]
            rw [hlookup]
            exact
              (wordToEdgeLabelling_eq_zero_of_finiteWordAllZeroB
                (coordinatesAt head) [] rfl).trans
              (wordToEdgeLabelling_eq_zero_of_finiteWordAllZeroB
                (coordinatesAt head) (wordAt head) hzero).symm
      · have htail : link ∈ tail := by
          rcases List.mem_cons.mp hlink with hhead | htail
          · exact False.elim (hsame hhead.symm)
          · exact htail
        have ih := wordToEdgeLabelling_sparseAuxiliaryDropWordsFrom
          coordinatesAt wordAt tail link hparts.2 htail
        cases hzero : finiteWordAllZeroB (wordAt head) with
        | false =>
            simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
              Bool.false_eq_true, ↓reduceIte,
              slabAuxiliaryDropWordAt, hsame]
            exact ih
        | true =>
            simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
              ↓reduceIte]
            exact ih

/-- Zero-row erasure never increases the number of table rows. -/
theorem slabSparseAuxiliaryDropWordsFrom_length_le
    (wordAt : SlabLink -> List Nat) : forall links : List SlabLink,
    (slabSparseAuxiliaryDropWordsFrom links wordAt).length <= links.length
  | [] => Nat.le_refl 0
  | head :: tail => by
      have ih := slabSparseAuxiliaryDropWordsFrom_length_le wordAt tail
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte, List.length_cons]
          omega
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            ↓reduceIte, List.length_cons]
          omega

/-- Every retained sparse row has a genuinely nonzero word. -/
theorem finiteWordAllZeroB_eq_false_of_mem_sparse
    (wordAt : SlabLink -> List Nat) : forall
    (links : List SlabLink) (entry : SlabLink × List Nat),
    entry ∈ slabSparseAuxiliaryDropWordsFrom links wordAt ->
      finiteWordAllZeroB entry.2 = false
  | [], entry, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, entry, hmem => by
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte] at hmem
          rcases List.mem_cons.mp hmem with heq | htail
          · subst entry
            exact hzero
          · exact finiteWordAllZeroB_eq_false_of_mem_sparse
              wordAt tail entry htail
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            ↓reduceIte] at hmem
          exact finiteWordAllZeroB_eq_false_of_mem_sparse
            wordAt tail entry hmem

/-! ## 3. The sparse rooted-component code and its exact decoding -/

/-- Serialize a rooted component while omitting all zero auxiliary rows. -/
def SlabFusionWitnessFaceStrandSeed.sparseDropCode
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
  auxiliaryWords := slabSparseAuxiliaryDropWordsFrom links
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)

/-- Sparse encoding leaves the already-sparse physical word unchanged. -/
theorem SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_sparseDropCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).decodePhysicalDrop =
      SlabFusionWitnessFaceStrandSeed.physicalDrop seed := by
  funext faceId
  unfold SlabFaceStrandComponentDropCode.decodePhysicalDrop
    SlabFusionWitnessFaceStrandSeed.sparseDropCode
    SlabFusionWitnessFaceStrandSeed.physicalDrop
  exact
    YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight.SlabFusionWitnessFaceStrandSeed.peelFaces_count
      seed faceId

/-- On a duplicate-free carrier, sparse encoding decodes to exactly the same
supported internal drop as the full code at each displayed link. -/
theorem SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_sparseDropCode
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup)
    (link : SlabLink) (hlink : link ∈ links) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).decodeAuxiliaryDrop
        extent link =
      edgeLabellingSupportedOn
        (canonicalUsedAuxiliaryCoordinates
          (slabIncidentPlaqIds extent link).length)
        (seed.atLinkSelection ⟨link, hlink⟩).drop := by
  let coordinatesAt : SlabLink -> List Nat := fun localLink =>
    canonicalUsedAuxiliaryCoordinates
      (slabIncidentPlaqIds extent localLink).length
  let wordAt := SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed
  have hdecode := wordToEdgeLabelling_sparseAuxiliaryDropWordsFrom
    coordinatesAt wordAt links link hnodup hlink
  have hdegree :
      (slabIncidentPlaqIds extent link).length <= linkIncidenceBound :=
    slabIncidentPlaqIds_length_le_six extent link
  unfold SlabFaceStrandComponentDropCode.decodeAuxiliaryDrop
    SlabFusionWitnessFaceStrandSeed.sparseDropCode
  change wordToEdgeLabelling (coordinatesAt link)
      (slabAuxiliaryDropWordAt link
        (slabSparseAuxiliaryDropWordsFrom links wordAt)) = _
  rw [hdecode]
  change wordToEdgeLabelling (coordinatesAt link)
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed link) = _
  rw [SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
    seed link hlink]
  exact wordToEdgeLabelling_map_eq_supportedOn
    (seed.atLinkSelection ⟨link, hlink⟩).drop
    (coordinatesAt link)
    (canonicalUsedAuxiliaryCoordinates_nodup hdegree)

/-- Sparse encoding cannot retain more rows than there are displayed links. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords.length
      <= links.length := by
  unfold SlabFusionWitnessFaceStrandSeed.sparseDropCode
  exact slabSparseAuxiliaryDropWordsFrom_length_le
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed) links

/-- Every row actually stored by sparse encoding is nonzero. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_nonzero
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords) :
    finiteWordAllZeroB entry.2 = false := by
  unfold SlabFusionWitnessFaceStrandSeed.sparseDropCode at hentry
  exact finiteWordAllZeroB_eq_false_of_mem_sparse
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    links entry hentry

/-! ## 4. Sparse-code whole-configuration reconstruction -/

/-- The sparse code reconstructs the exact physical source from the accepted
lowered physical target. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructPhysical
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).reconstructPhysical
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop.SlabFusionWitnessFaceStrandSeed.lowerPhysical
          seed) = physical := by
  unfold SlabFaceStrandComponentDropCode.reconstructPhysical
  rw [SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_sparseDropCode seed]
  exact SlabFusionWitnessFaceStrandSeed.reconstructPhysical_eq seed

/-- The sparse code reconstructs each displayed source auxiliary lookup. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAuxiliaryAt
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup)
    (link : SlabLink) (hlink : link ∈ links) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).reconstructAuxiliaryAt
        extent
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed)
        link =
      slabFusionWitnessAssignmentAt link assignment := by
  unfold SlabFaceStrandComponentDropCode.reconstructAuxiliaryAt
  rw [YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment_atLink
    seed link hlink]
  rw [SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_sparseDropCode
    seed hnodup link hlink]
  exact
    SlabLinkPartnerClosedFaceSelection.reconstructAuxiliary_lower
      (seed.atLinkSelection ⟨link, hlink⟩)

/-- **Sparse finite-code global left inverse.**  The sparse code and accepted
lowered target recover the literal source assignment. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (hnodup : links.Nodup) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).reconstructAssignment
        extent links
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed) = assignment := by
  calc
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).reconstructAssignment
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
      exact
        SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAuxiliaryAt
          seed hnodup link hlink
    _ = assignment := slabFusionWitnessAssignmentFrom_at_eq
      K extent physical links assignment hnodup hassignment

/-- The production complete slab carrier supplies duplicate-freeness to the
sparse global left inverse. -/
theorem SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructCompleteAssignment
    {K extent : Nat} {physical : SlabLabelling}
    {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical
        (boundaryCompleteSlabLinks extent)}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical (boundaryCompleteSlabLinks extent)
        assignment hassignment) :
    (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).reconstructAssignment
        extent (boundaryCompleteSlabLinks extent)
        (YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment.SlabFusionWitnessFaceStrandSeed.lowerAssignment
          seed) = assignment :=
  SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAssignment seed
    (boundaryCompleteSlabLinks_nodup extent)

#print axioms finiteWordAllZeroB
#print axioms wordToEdgeLabelling_eq_zero_of_finiteWordAllZeroB
#print axioms slabSparseAuxiliaryDropWordsFrom
#print axioms slabAuxiliaryDropWordAt_sparseFrom_of_not_mem
#print axioms wordToEdgeLabelling_sparseAuxiliaryDropWordsFrom
#print axioms slabSparseAuxiliaryDropWordsFrom_length_le
#print axioms finiteWordAllZeroB_eq_false_of_mem_sparse
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode
#print axioms SlabFusionWitnessFaceStrandSeed.decodePhysicalDrop_sparseDropCode
#print axioms SlabFusionWitnessFaceStrandSeed.decodeAuxiliaryDrop_sparseDropCode
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_auxiliaryWords_length_le
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_nonzero
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructPhysical
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAuxiliaryAt
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructAssignment
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCode_reconstructCompleteAssignment

end YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
