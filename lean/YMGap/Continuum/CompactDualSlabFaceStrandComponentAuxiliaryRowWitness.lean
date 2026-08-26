/-
# Every retained auxiliary row reaches a selected physical component copy

Sparse auxiliary rows are useful for entropy only if they can be charged to
the rooted physical component.  This module proves the first load-bearing
geometric direction.

A nonzero encoded word contains a positive compiled drop.  Positivity of that
finite Boolean count returns an actual selected edge slot.  The executable
edge-slot descent must therefore have found a real resolved-network port, and
the already-constructed canonical strand terminal of that port is a selected
physical face copy incident on the same slab link.

The final compiler takes membership of an arbitrary row in the sparse code
and returns the displayed-link membership proof together with such a selected
physical terminal.  No orientation, port, or component witness is added to the
stored code; all of it is reconstructed from row nonzeroness.

Constructive contract: every existence result is a `Type`-level sigma witness
computed by finite recursion.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, noncomputable declaration, or enlarged heartbeat
budget.
-/

import YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode

namespace YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandComponentSparseDropCode
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.CompactDualSlabPhysicalSelectionPullback
open YMGap.Continuum.ResolvedTrivalentNetworkPortSelectionRemoval
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.ResolvedTrivalentNetworkSelectionRemoval
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Data-bearing witnesses for positive finite Boolean counts -/

/-- A positive finite Boolean interval count computes an actual selected
offset in that interval. -/
def boolCountFromPositiveWitness
    (selected : Nat -> Bool) (start : Nat) : forall length : Nat,
    0 < boolCountFrom selected start length ->
      {offset : Fin length // selected (start + offset.val) = true}
  | 0, hpositive => by
      simp [boolCountFrom] at hpositive
  | length + 1, hpositive => by
      cases hselected : selected start with
      | true =>
          exact ⟨⟨0, by omega⟩, by simpa using hselected⟩
      | false =>
          have htail :
              0 < boolCountFrom selected (start + 1) length := by
            simpa [boolCountFrom, boolIndicator, hselected] using hpositive
          let witness := boolCountFromPositiveWitness
            selected (start + 1) length htail
          refine ⟨Fin.succ witness.1, ?_⟩
          have hindex :
              start + (Fin.succ witness.1).val =
                start + 1 + witness.1.val := by
            simp only [Fin.val_succ]
            omega
          rw [hindex]
          exact witness.property

/-- A finite word rejected by the all-zero test computes the position of an
actual nonzero entry.  Retaining the position avoids any choice from a
propositional list-membership witness. -/
def finiteWordNonzeroIndexWitness : forall word : List Nat,
    finiteWordAllZeroB word = false ->
      {index : Fin word.length // word.get index ≠ 0}
  | [], hzero => by
      simp [finiteWordAllZeroB] at hzero
  | head :: tail, hzero => by
      by_cases hhead : head = 0
      · have htail : finiteWordAllZeroB tail = false := by
          simpa [finiteWordAllZeroB, hhead] using hzero
        let witness := finiteWordNonzeroIndexWitness tail htail
        exact ⟨Fin.succ witness.1, by simpa using witness.property⟩
      · exact ⟨⟨0, by simp⟩, by simpa using hhead⟩

/-! ## 2. Positive local drop reaches a selected physical terminal -/

/-- A selected physical terminal produced from one link selection. -/
abbrev SlabLinkSelectedPhysicalTerminal
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem) :=
  {terminal : SlabLinkPhysicalStrandTerminal
      cutoff extent physical link auxiliary hmem //
    selection.selected
      (slabLinkPhysicalTerminalFaceStrandCopy
        cutoff extent physical link auxiliary hmem terminal) = true}

/-- A true proof-independent edge-slot value computes the actual resolved
port found by the executable descent, together with its exact address and
selection value. -/
def ResolvedNetworkPortClosedSelection.portOfEdgeSlotTrue
    {vertices : List TrivalentVertex} {label : EdgeLabelling}
    {network : ResolvedTrivalentNetwork vertices label}
    (selection : ResolvedNetworkPortClosedSelection network)
    (edge slot : Nat)
    (htrue : selection.edgeSlotValue edge slot = true) :
    {port : ResolvedNetworkPort network //
      port.edgeId = edge ∧ port.slot = slot ∧
        selection.selected port = true} := by
  unfold ResolvedNetworkPortClosedSelection.edgeSlotValue at htrue
  cases hfind : (allResolvedNetworkPorts network).find?
      (portHasEdgeSlot edge slot) with
  | none =>
      rw [hfind] at htrue
      contradiction
  | some port =>
      have hfiber := List.find?_some hfind
      have hparts := (Bool.and_eq_true _ _).mp hfiber
      refine ⟨port, of_decide_eq_true hparts.1,
        of_decide_eq_true hparts.2, ?_⟩
      simpa [hfind] using htrue

/-- Any positive compiled edge drop returns a selected physical terminal of
the same accepted resolved link.  Terminal extraction supplies the geometric
path from the found edge slot to that physical copy. -/
def SlabLinkPartnerClosedFaceSelection.selectedPhysicalTerminalOfDropPos
    {cutoff extent : Nat} {physical : SlabLabelling} {link : SlabLink}
    {auxiliary : SlabLabelling}
    {hmem : auxiliary ∈
      slabLinkFusionWitnesses cutoff extent physical link}
    (selection : SlabLinkPartnerClosedFaceSelection
      cutoff extent physical link auxiliary hmem)
    (edge : Nat) (hpositive : 0 < selection.drop edge) :
    SlabLinkSelectedPhysicalTerminal selection := by
  unfold SlabLinkPartnerClosedFaceSelection.drop at hpositive
  let portSelection := selection.toCanonical.toPortClosedSelection
  let label := canonicalLinkLabelling
    (slabIncidentPlaqIds extent link).length
    (slabLinkExternalSpins extent physical link) auxiliary
  have hcount : 0 < boolCountFrom
      (portSelection.edgeSlotValue edge) 0 (label edge) := by
    exact hpositive
  let witness := boolCountFromPositiveWitness
    (portSelection.edgeSlotValue edge) 0 (label edge) hcount
  have hvalue : portSelection.edgeSlotValue edge witness.1.val = true := by
    simpa only [Nat.zero_add] using witness.property
  let portWitness :=
    YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness.ResolvedNetworkPortClosedSelection.portOfEdgeSlotTrue
      portSelection edge witness.1.val hvalue
  let terminal := canonicalLinkStrandTerminal
    (slabIncidentPlaqIds_length_le_six extent link)
    (slabLinkFusionWitness_mem_allowed
      cutoff extent physical link auxiliary hmem)
    portWitness.1
  refine ⟨terminal, ?_⟩
  change selection.toCanonical.toPortClosedSelection.selected
      portWitness.1 = true
  exact portWitness.property.2.2

/-! ## 3. Recover the source field of an arbitrary retained sparse row -/

/-- The source link and prescribed word underlying one sparse table row. -/
structure SparseAuxiliaryDropRowSource
    (links : List SlabLink) (wordAt : SlabLink -> List Nat)
    (entry : SlabLink × List Nat) : Type where
  link_mem : entry.1 ∈ links
  word_eq : entry.2 = wordAt entry.1

/-- Every sparse row key belongs to the source link carrier. -/
theorem sparseAuxiliaryDropRow_link_mem
    (wordAt : SlabLink -> List Nat) : forall
    (links : List SlabLink) (entry : SlabLink × List Nat),
    entry ∈ slabSparseAuxiliaryDropWordsFrom links wordAt ->
      entry.1 ∈ links
  | [], entry, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, entry, hmem => by
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte] at hmem
          rcases List.mem_cons.mp hmem with heq | htail
          · subst entry
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem head
              (sparseAuxiliaryDropRow_link_mem wordAt tail entry htail)
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            ↓reduceIte] at hmem
          exact List.mem_cons_of_mem head
            (sparseAuxiliaryDropRow_link_mem wordAt tail entry hmem)

/-- Every sparse row value is the prescribed word at its retained key. -/
theorem sparseAuxiliaryDropRow_word_eq
    (wordAt : SlabLink -> List Nat) : forall
    (links : List SlabLink) (entry : SlabLink × List Nat),
    entry ∈ slabSparseAuxiliaryDropWordsFrom links wordAt ->
      entry.2 = wordAt entry.1
  | [], entry, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, entry, hmem => by
      cases hzero : finiteWordAllZeroB (wordAt head) with
      | false =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            Bool.false_eq_true, ↓reduceIte] at hmem
          rcases List.mem_cons.mp hmem with heq | htail
          · subst entry
            rfl
          · exact sparseAuxiliaryDropRow_word_eq
              wordAt tail entry htail
      | true =>
          simp only [slabSparseAuxiliaryDropWordsFrom, hzero,
            ↓reduceIte] at hmem
          exact sparseAuxiliaryDropRow_word_eq
            wordAt tail entry hmem

/-- Membership in a sparse table computes both membership of its key in the
source carrier and equality with the prescribed source word. -/
def sparseAuxiliaryDropRowSource
    (wordAt : SlabLink -> List Nat) : forall
    (links : List SlabLink) (entry : SlabLink × List Nat),
    entry ∈ slabSparseAuxiliaryDropWordsFrom links wordAt ->
      SparseAuxiliaryDropRowSource links wordAt entry
  | links, entry, hmem =>
      ⟨sparseAuxiliaryDropRow_link_mem wordAt links entry hmem,
        sparseAuxiliaryDropRow_word_eq wordAt links entry hmem⟩

/-- The data reconstructed from a retained rooted-component row: its actual
displayed-link membership and a selected physical terminal on that link. -/
structure SlabSparseAuxiliaryRowPhysicalWitness
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat) : Type where
  link_mem : entry.1 ∈ links
  selectedTerminal : SlabLinkSelectedPhysicalTerminal
    (seed.atLinkSelection ⟨entry.1, link_mem⟩)

/-- **Retained-row charging witness.**  Every row in the sparse component
code computes a selected physical terminal incident on that row's link. -/
def SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalWitness
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (entry : SlabLink × List Nat)
    (hentry : entry ∈
      (SlabFusionWitnessFaceStrandSeed.sparseDropCode seed).auxiliaryWords) :
    SlabSparseAuxiliaryRowPhysicalWitness seed entry := by
  have hentryRaw : entry ∈ slabSparseAuxiliaryDropWordsFrom links
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed) := by
    exact hentry
  let source := sparseAuxiliaryDropRowSource
    (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt seed)
    links entry hentryRaw
  let hlink : entry.1 ∈ links := source.link_mem
  let selection := seed.atLinkSelection ⟨entry.1, hlink⟩
  have hword : entry.2 =
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds extent entry.1).length).map selection.drop :=
    source.word_eq.trans
      (SlabFusionWitnessFaceStrandSeed.auxiliaryDropWordAt_of_mem
        seed entry.1 hlink)
  have hnonzero : finiteWordAllZeroB entry.2 = false :=
    SlabFusionWitnessFaceStrandSeed.sparseDropCode_row_nonzero
      seed entry hentry
  let coordinates := canonicalUsedAuxiliaryCoordinates
    (slabIncidentPlaqIds extent entry.1).length
  have hencodedNonzero :
      finiteWordAllZeroB (coordinates.map selection.drop) = false := by
    rw [← hword]
    exact hnonzero
  let indexWitness := finiteWordNonzeroIndexWitness
    (coordinates.map selection.drop) hencodedNonzero
  let coordinateIndex : Fin coordinates.length :=
    ⟨indexWitness.1.val, by
      simpa only [List.length_map] using indexWitness.1.isLt⟩
  let edge := coordinates.get coordinateIndex
  have hdropNe : selection.drop edge ≠ 0 := by
    simpa [edge, coordinateIndex] using indexWitness.property
  have hdropPos : 0 < selection.drop edge := by omega
  exact ⟨hlink,
    SlabLinkPartnerClosedFaceSelection.selectedPhysicalTerminalOfDropPos
      selection edge hdropPos⟩

#print axioms boolCountFromPositiveWitness
#print axioms finiteWordNonzeroIndexWitness
#print axioms SlabLinkSelectedPhysicalTerminal
#print axioms ResolvedNetworkPortClosedSelection.portOfEdgeSlotTrue
#print axioms SlabLinkPartnerClosedFaceSelection.selectedPhysicalTerminalOfDropPos
#print axioms SparseAuxiliaryDropRowSource
#print axioms sparseAuxiliaryDropRow_link_mem
#print axioms sparseAuxiliaryDropRow_word_eq
#print axioms sparseAuxiliaryDropRowSource
#print axioms SlabSparseAuxiliaryRowPhysicalWitness
#print axioms SlabFusionWitnessFaceStrandSeed.sparseDropCodeRowPhysicalWitness

end YMGap.Continuum.CompactDualSlabFaceStrandComponentAuxiliaryRowWitness
