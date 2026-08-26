/-
# Constructive physical-terminal extraction for canonical link strands

Strict path progress is contracted here into the promised witness.  A strand
path is an inductive `Type`: it either stops at an actual physical port or
takes the uniquely defined full internal advance and continues.  An oriented
state remembers two successive internal ports; its explicit end-distance
rank strictly decreases when the next port is internal.

Well-founded recursion therefore returns both a physical terminal and the
strand path reaching it from every canonical resolved port.  The path witness
is retained for the forthcoming endpoint-pairing and reversal proofs.

Constructive contract: recursion on the proved natural rank, with every
branch selected by the existing decidable physical/internal classifier.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkStrandStrictProgress

namespace YMGap.Continuum.CanonicalLinkStrandTerminal

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkStrandMonotonePath
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandStrictProgress
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. Full internal advance and witnessed strand paths -/

/-- The full strand advance from a known internal port: cross the internal
edge with the same slot, then take the local trivalent mate. -/
def canonicalInternalAdvancePort
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (occurrence : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hinternal : occurrence.edgeId ∈
      canonicalInternalFusionEdges degree) :
    ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed) :=
  (canonicalInternalStrandContinue hdegree hallowed hinternal
    (⟨occurrence, rfl⟩ : CanonicalInternalStrandPort
      occurrence.edgeId external auxiliary hallowed)).1.localMate

/-- A data-bearing proof that repeated full internal advances from `start`
reach the displayed physical terminal. -/
inductive CanonicalStrandPathToPhysical
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :
    ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed) →
      CanonicalPhysicalStrandPort external auxiliary hallowed → Type
  | stop (terminal : CanonicalPhysicalStrandPort
      external auxiliary hallowed) :
      CanonicalStrandPathToPhysical hdegree hallowed terminal.1 terminal
  | advance
      (source : ResolvedNetworkPort
        (canonicalLinkResolvedStrandNetwork
          degree external auxiliary hallowed))
      (hinternal : source.edgeId ∈ canonicalInternalFusionEdges degree)
      (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed)
      (tail : CanonicalStrandPathToPhysical hdegree hallowed
        (canonicalInternalAdvancePort
          hdegree hallowed source hinternal) terminal) :
      CanonicalStrandPathToPhysical hdegree hallowed source terminal

/-- Terminal data together with the actual strand path from `start`. -/
abbrev CanonicalStrandTerminalWitness
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :=
  Σ terminal : CanonicalPhysicalStrandPort external auxiliary hallowed,
    CanonicalStrandPathToPhysical hdegree hallowed start terminal

/-! ## 2. Oriented internal states and their decreasing rank -/

/-- An oriented state consists of an internal source whose full advance is
also internal.  Thus it records two successive internal ports without an
extra equality field: the current port is computed from the source. -/
structure CanonicalOrientedInternalState
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) : Type where
  source : ResolvedNetworkPort
    (canonicalLinkResolvedStrandNetwork
      degree external auxiliary hallowed)
  sourceInternal : source.edgeId ∈ canonicalInternalFusionEdges degree
  currentInternal :
    (canonicalInternalAdvancePort
      hdegree hallowed source sourceInternal).edgeId ∈
        canonicalInternalFusionEdges degree

/-- The current port of an oriented state. -/
def CanonicalOrientedInternalState.current
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed) :=
  canonicalInternalAdvancePort
    hdegree hallowed state.source state.sourceInternal

/-- The next full internal advance from the current port. -/
def CanonicalOrientedInternalState.nextPort
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed) :=
  canonicalInternalAdvancePort
    hdegree hallowed state.current state.currentInternal

/-- The strictly decreasing end-distance rank of an oriented state. -/
def CanonicalOrientedInternalState.rank
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed) : Nat :=
  natPathRank (canonicalLinkVertices degree).length
    state.source.vertexIndex.val state.current.vertexIndex.val

/-- If the next port is internal, shift the oriented window forward by one
full advance. -/
def CanonicalOrientedInternalState.next
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed)
    (hnextInternal : state.nextPort.edgeId ∈
      canonicalInternalFusionEdges degree) :
    CanonicalOrientedInternalState hdegree hallowed where
  source := state.current
  sourceInternal := state.currentInternal
  currentInternal := hnextInternal

/-- Shifting an oriented internal window strictly decreases its rank. -/
theorem CanonicalOrientedInternalState.next_rank_lt
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed)
    (hnextInternal : state.nextPort.edgeId ∈
      canonicalInternalFusionEdges degree) :
    (state.next hnextInternal).rank < state.rank := by
  let firstCrossed := canonicalInternalStrandContinue
    hdegree hallowed state.sourceInternal
      (⟨state.source, rfl⟩ : CanonicalInternalStrandPort
        state.source.edgeId external auxiliary hallowed)
  let secondCrossed := canonicalInternalStrandContinue
    hdegree hallowed state.currentInternal
      (⟨state.current, rfl⟩ : CanonicalInternalStrandPort
        state.current.edgeId external auxiliary hallowed)
  have hprogress := canonicalSuccessiveInternalCrossing_rank_decreases
    hdegree hallowed state.sourceInternal
      (⟨state.source, rfl⟩ : CanonicalInternalStrandPort
        state.source.edgeId external auxiliary hallowed)
      state.currentInternal
  change natPathRank (canonicalLinkVertices degree).length
        state.current.vertexIndex.val state.nextPort.vertexIndex.val <
      natPathRank (canonicalLinkVertices degree).length
        state.source.vertexIndex.val state.current.vertexIndex.val
  change natPathRank (canonicalLinkVertices degree).length
        firstCrossed.1.localMate.vertexIndex.val
        secondCrossed.1.localMate.vertexIndex.val <
      natPathRank (canonicalLinkVertices degree).length
        state.source.vertexIndex.val
        firstCrossed.1.localMate.vertexIndex.val
  rw [ResolvedNetworkPort.localMate_vertexIndex firstCrossed.1,
    ResolvedNetworkPort.localMate_vertexIndex secondCrossed.1]
  exact hprogress

/-! ## 3. Well-founded terminal extraction -/

/-- Starting at the current port of an oriented internal state, recursively
return a physical terminal and the exact strand path reaching it. -/
def CanonicalOrientedInternalState.terminalWitness
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed) :
    CanonicalStrandTerminalWitness hdegree hallowed state.current :=
  let nextPort := state.nextPort
  match canonicalResolvedPortClassify hdegree hallowed nextPort with
  | .physical hphysical =>
      let terminal : CanonicalPhysicalStrandPort
          external auxiliary hallowed := ⟨nextPort, hphysical⟩
      ⟨terminal,
        CanonicalStrandPathToPhysical.advance state.current
          state.currentInternal terminal
          (CanonicalStrandPathToPhysical.stop terminal)⟩
  | .internal hnextInternal =>
      let tail := (state.next hnextInternal).terminalWitness
      ⟨tail.1,
        CanonicalStrandPathToPhysical.advance state.current
          state.currentInternal tail.1 tail.2⟩
termination_by state.rank
decreasing_by exact state.next_rank_lt hnextInternal

/-- Every canonical resolved strand port constructively reaches a physical
terminal, with the complete internal-advance path retained as data. -/
def canonicalLinkStrandTerminalWitness
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    CanonicalStrandTerminalWitness hdegree hallowed start :=
  match canonicalResolvedPortClassify hdegree hallowed start with
  | .physical hphysical =>
      let terminal : CanonicalPhysicalStrandPort
          external auxiliary hallowed := ⟨start, hphysical⟩
      ⟨terminal, CanonicalStrandPathToPhysical.stop terminal⟩
  | .internal hstartInternal =>
      let firstPort := canonicalInternalAdvancePort
        hdegree hallowed start hstartInternal
      match canonicalResolvedPortClassify hdegree hallowed firstPort with
      | .physical hphysical =>
          let terminal : CanonicalPhysicalStrandPort
              external auxiliary hallowed := ⟨firstPort, hphysical⟩
          ⟨terminal,
            CanonicalStrandPathToPhysical.advance start hstartInternal
              terminal (CanonicalStrandPathToPhysical.stop terminal)⟩
      | .internal hfirstInternal =>
          let state : CanonicalOrientedInternalState hdegree hallowed :=
            { source := start
              sourceInternal := hstartInternal
              currentInternal := hfirstInternal }
          let tail := state.terminalWitness
          ⟨tail.1,
            CanonicalStrandPathToPhysical.advance start hstartInternal
              tail.1 tail.2⟩

/-- The physical terminal computed from any canonical resolved strand port. -/
def canonicalLinkStrandTerminal
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)) :
    CanonicalPhysicalStrandPort external auxiliary hallowed :=
  (canonicalLinkStrandTerminalWitness hdegree hallowed start).1

#print axioms canonicalInternalAdvancePort
#print axioms CanonicalStrandPathToPhysical
#print axioms CanonicalStrandTerminalWitness
#print axioms CanonicalOrientedInternalState
#print axioms CanonicalOrientedInternalState.current
#print axioms CanonicalOrientedInternalState.nextPort
#print axioms CanonicalOrientedInternalState.rank
#print axioms CanonicalOrientedInternalState.next
#print axioms CanonicalOrientedInternalState.next_rank_lt
#print axioms CanonicalOrientedInternalState.terminalWitness
#print axioms canonicalLinkStrandTerminalWitness
#print axioms canonicalLinkStrandTerminal

end YMGap.Continuum.CanonicalLinkStrandTerminal
