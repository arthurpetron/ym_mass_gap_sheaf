/-
# Fixed-point-free physical-terminal pairing on one canonical link

The terminal partner is already an involution.  To exclude fixed points, this
module proves the remaining geometric fact: once two successive internal
ports orient the canonical fusion path, every retained advance continues in
that direction, so the physical terminal lies strictly beyond the current
vertex.  Hence a strand beginning at the local mate of a physical port cannot
return to that port's vertex.

The resulting partner is therefore both involutive and fixed-point-free: the
actual local physical-terminal pairing needed before global face gluing.

Constructive contract: structural induction on retained strand paths and
explicit natural-order transitivity.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner

namespace YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing

set_option autoImplicit false

open YMGap.Continuum.CanonicalLinkEdgeOccurrenceMultiplicity
open YMGap.Continuum.CanonicalLinkInternalEdgeEndpoints
open YMGap.Continuum.CanonicalLinkInternalHalfEdgeSwap
open YMGap.Continuum.CanonicalLinkInternalStrandContinuation
open YMGap.Continuum.CanonicalLinkPhysicalTerminalPartner
open YMGap.Continuum.CanonicalLinkStrandMonotonePath
open YMGap.Continuum.CanonicalLinkStrandPathTopology
open YMGap.Continuum.CanonicalLinkStrandStep
open YMGap.Continuum.CanonicalLinkStrandStrictProgress
open YMGap.Continuum.CanonicalLinkStrandTerminal
open YMGap.Continuum.CompactDualSlabLinkStrandResolution
open YMGap.Continuum.ResolvedTrivalentNetworkHalfEdges
open YMGap.Continuum.ResolvedTrivalentNetworkPorts
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution

/-! ## 1. Every oriented state takes one more step in the same direction -/

/-- The source, current, and next vertices of an oriented internal state are
three consecutive positions with one common direction. -/
theorem canonicalOrientedInternalState_step_direction
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed) :
    (state.source.vertexIndex.val + 1 = state.current.vertexIndex.val ∧
        state.current.vertexIndex.val + 1 = state.nextPort.vertexIndex.val) ∨
      (state.current.vertexIndex.val + 1 = state.source.vertexIndex.val ∧
        state.nextPort.vertexIndex.val + 1 = state.current.vertexIndex.val) := by
  let firstTyped : CanonicalInternalStrandPort
      state.source.edgeId external auxiliary hallowed := ⟨state.source, rfl⟩
  let firstCrossed := canonicalInternalStrandContinue
    hdegree hallowed state.sourceInternal firstTyped
  let secondTyped : CanonicalInternalStrandPort
      state.current.edgeId external auxiliary hallowed := ⟨state.current, rfl⟩
  let secondCrossed := canonicalInternalStrandContinue
    hdegree hallowed state.currentInternal secondTyped

  have hfirst := canonicalInternalStrandContinue_vertexIndex_adjacent
    hdegree hallowed state.sourceInternal firstTyped
  change firstCrossed.1.vertexIndex.val + 1 =
        state.source.vertexIndex.val ∨
      state.source.vertexIndex.val + 1 =
        firstCrossed.1.vertexIndex.val at hfirst
  have hfirstMate : state.current.vertexIndex =
      firstCrossed.1.vertexIndex :=
    ResolvedNetworkPort.localMate_vertexIndex firstCrossed.1

  have hsecond := canonicalInternalStrandContinue_vertexIndex_adjacent
    hdegree hallowed state.currentInternal secondTyped
  change secondCrossed.1.vertexIndex.val + 1 =
        state.current.vertexIndex.val ∨
      state.current.vertexIndex.val + 1 =
        secondCrossed.1.vertexIndex.val at hsecond
  have hsecondMate : state.nextPort.vertexIndex =
      secondCrossed.1.vertexIndex :=
    ResolvedNetworkPort.localMate_vertexIndex secondCrossed.1

  have hnoReturnFin := canonicalSuccessiveInternalCrossing_no_return
    hdegree hallowed state.sourceInternal firstTyped state.currentInternal
  have hnoReturn : state.nextPort.vertexIndex.val ≠
      state.source.vertexIndex.val := by
    intro heq
    apply hnoReturnFin
    apply Fin.ext
    exact hsecondMate.symm ▸ heq

  apply natPathAdjacent_nonbacktracking_direction
  · unfold NatPathAdjacent
    rw [hfirstMate]
    exact hfirst.symm
  · unfold NatPathAdjacent
    rw [hsecondMate]
    exact hsecond.symm
  · exact hnoReturn

/-- In the increasing case, the next vertex is strictly above the current
vertex. -/
theorem canonicalOrientedInternalState_current_lt_next_of_source_lt_current
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed)
    (hsource : state.source.vertexIndex.val <
      state.current.vertexIndex.val) :
    state.current.vertexIndex.val < state.nextPort.vertexIndex.val := by
  rcases canonicalOrientedInternalState_step_direction state with
      hincreasing | hdecreasing
  · exact Nat.lt_of_succ_le (Nat.le_of_eq hincreasing.2)
  · have hreverse : state.current.vertexIndex.val <
        state.source.vertexIndex.val :=
      Nat.lt_of_succ_le (Nat.le_of_eq hdecreasing.1)
    exact False.elim (Nat.lt_asymm hsource hreverse)

/-- In the decreasing case, the next vertex is strictly below the current
vertex. -/
theorem canonicalOrientedInternalState_next_lt_current_of_current_lt_source
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    (state : CanonicalOrientedInternalState hdegree hallowed)
    (hsource : state.current.vertexIndex.val <
      state.source.vertexIndex.val) :
    state.nextPort.vertexIndex.val < state.current.vertexIndex.val := by
  rcases canonicalOrientedInternalState_step_direction state with
      hincreasing | hdecreasing
  · have hreverse : state.source.vertexIndex.val <
        state.current.vertexIndex.val :=
      Nat.lt_of_succ_le (Nat.le_of_eq hincreasing.1)
    exact False.elim (Nat.lt_asymm hsource hreverse)
  · exact Nat.lt_of_succ_le (Nat.le_of_eq hdecreasing.2)

/-! ## 2. A retained oriented path ends strictly beyond its current vertex -/

/-- Along a terminal path starting at the current port of an oriented state,
the terminal remains strictly beyond that current vertex in the direction
selected by the source-current pair. -/
theorem canonicalOrientedInternalState_path_terminal_beyond
    {degree : Nat} {external auxiliary : EdgeLabelling}
    {hdegree : degree ≤ linkIncidenceBound}
    {hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true}
    {start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed)}
    {terminal : CanonicalPhysicalStrandPort external auxiliary hallowed}
    (path : CanonicalStrandPathToPhysical
      hdegree hallowed start terminal) :
    (state : CanonicalOrientedInternalState hdegree hallowed) →
    state.current = start →
      (state.source.vertexIndex.val < state.current.vertexIndex.val →
          state.current.vertexIndex.val < terminal.1.vertexIndex.val) ∧
        (state.current.vertexIndex.val < state.source.vertexIndex.val →
          terminal.1.vertexIndex.val < state.current.vertexIndex.val) := by
  induction path with
  | stop terminal =>
      intro state hstart
      have hphysical : state.current.edgeId < degree := by
        rw [hstart]
        exact terminal.2
      exact False.elim
        ((canonicalInternalFusionEdge_not_lt
          hdegree state.currentInternal) hphysical)
  | advance source hinternal terminal tail ih =>
      intro state hstart
      cases hstart
      match hclass : canonicalResolvedPortClassify
          hdegree hallowed state.nextPort with
      | .physical hphysical =>
          let nextTerminal : CanonicalPhysicalStrandPort
              external auxiliary hallowed := ⟨state.nextPort, hphysical⟩
          have hterminal : terminal = nextTerminal :=
            canonicalStrandPath_terminal_unique tail
              (CanonicalStrandPathToPhysical.stop nextTerminal)
          constructor
          · intro hsource
            have hstep :=
              canonicalOrientedInternalState_current_lt_next_of_source_lt_current
                state hsource
            rw [hterminal]
            exact hstep
          · intro hsource
            have hstep :=
              canonicalOrientedInternalState_next_lt_current_of_current_lt_source
                state hsource
            rw [hterminal]
            exact hstep
      | .internal hnextInternal =>
          let nextState := state.next hnextInternal
          have htail := ih nextState rfl
          constructor
          · intro hsource
            have hstep :=
              canonicalOrientedInternalState_current_lt_next_of_source_lt_current
                state hsource
            exact Nat.lt_trans hstep (htail.1 hstep)
          · intro hsource
            have hstep :=
              canonicalOrientedInternalState_next_lt_current_of_current_lt_source
                state hsource
            exact Nat.lt_trans (htail.2 hstep) hstep

/-! ## 3. Any nontrivial internal start ends at a different vertex -/

/-- A terminal path beginning at an internal port cannot finish at the same
vertex at which it began. -/
theorem canonicalInternalStart_terminal_vertexIndex_ne
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (start : ResolvedNetworkPort
      (canonicalLinkResolvedStrandNetwork
        degree external auxiliary hallowed))
    (hstartInternal : start.edgeId ∈ canonicalInternalFusionEdges degree)
    {terminal : CanonicalPhysicalStrandPort external auxiliary hallowed}
    (path : CanonicalStrandPathToPhysical
      hdegree hallowed start terminal) :
    terminal.1.vertexIndex ≠ start.vertexIndex := by
  cases path with
  | stop terminal =>
      exact False.elim
        ((canonicalInternalFusionEdge_not_lt
          hdegree hstartInternal) terminal.2)
  | advance source hinternal terminal tail =>
      let firstPort := canonicalInternalAdvancePort
        hdegree hallowed start hstartInternal
      match hclass : canonicalResolvedPortClassify
          hdegree hallowed firstPort with
      | .physical hphysical =>
          let firstTerminal : CanonicalPhysicalStrandPort
              external auxiliary hallowed := ⟨firstPort, hphysical⟩
          have hterminal : terminal = firstTerminal :=
            canonicalStrandPath_terminal_unique tail
              (CanonicalStrandPathToPhysical.stop firstTerminal)
          let crossed := canonicalInternalStrandContinue
            hdegree hallowed hstartInternal
              (⟨start, rfl⟩ : CanonicalInternalStrandPort
                start.edgeId external auxiliary hallowed)
          have hcrossNe := canonicalInternalStrandContinue_vertexIndex_ne
            hdegree hallowed hstartInternal
              (⟨start, rfl⟩ : CanonicalInternalStrandPort
                start.edgeId external auxiliary hallowed)
          have hfirstNe : firstPort.vertexIndex ≠ start.vertexIndex := by
            intro heq
            apply hcrossNe
            exact (ResolvedNetworkPort.localMate_vertexIndex crossed.1).symm.trans
              heq
          intro heq
          apply hfirstNe
          exact (congrArg
            (fun occurrence : CanonicalPhysicalStrandPort
              external auxiliary hallowed => occurrence.1.vertexIndex)
            hterminal).symm.trans heq
      | .internal hfirstInternal =>
          let state : CanonicalOrientedInternalState hdegree hallowed :=
            { source := start
              sourceInternal := hstartInternal
              currentInternal := hfirstInternal }
          have hbeyond := canonicalOrientedInternalState_path_terminal_beyond
            tail state rfl
          let crossed := canonicalInternalStrandContinue
            hdegree hallowed hstartInternal
              (⟨start, rfl⟩ : CanonicalInternalStrandPort
                start.edgeId external auxiliary hallowed)
          have hadjacent := canonicalInternalStrandContinue_vertexIndex_adjacent
            hdegree hallowed hstartInternal
              (⟨start, rfl⟩ : CanonicalInternalStrandPort
                start.edgeId external auxiliary hallowed)
          change crossed.1.vertexIndex.val + 1 = start.vertexIndex.val ∨
              start.vertexIndex.val + 1 = crossed.1.vertexIndex.val at hadjacent
          have hcurrentVertex : state.current.vertexIndex =
              crossed.1.vertexIndex :=
            ResolvedNetworkPort.localMate_vertexIndex crossed.1
          intro heq
          have heqVal : terminal.1.vertexIndex.val = start.vertexIndex.val :=
            congrArg Fin.val heq
          rcases hadjacent with hdecreasing | hincreasing
          · have hcurrentLt : state.current.vertexIndex.val <
                state.source.vertexIndex.val := by
              rw [hcurrentVertex]
              exact Nat.lt_of_succ_le (Nat.le_of_eq hdecreasing)
            have hterminalLt := hbeyond.2 hcurrentLt
            rw [heqVal] at hterminalLt
            exact Nat.lt_asymm hcurrentLt hterminalLt
          · have hsourceLt : state.source.vertexIndex.val <
                state.current.vertexIndex.val := by
              rw [hcurrentVertex]
              exact Nat.lt_of_succ_le (Nat.le_of_eq hincreasing)
            have hcurrentLtTerminal := hbeyond.1 hsourceLt
            rw [heqVal] at hcurrentLtTerminal
            exact Nat.lt_asymm hsourceLt hcurrentLtTerminal

/-! ## 4. The actual fixed-point-free pairing -/

/-- The canonical physical-terminal partner has no fixed point. -/
theorem canonicalPhysicalStrandPartner_ne_self
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    canonicalPhysicalStrandPartner hdegree hallowed terminal ≠ terminal := by
  intro hpartner
  have hpath := canonicalPhysicalStrandPartner_path
    hdegree hallowed terminal
  match hclass : canonicalResolvedPortClassify
      hdegree hallowed terminal.1.localMate with
  | .physical hphysical =>
      let mateTerminal : CanonicalPhysicalStrandPort
          external auxiliary hallowed := ⟨terminal.1.localMate, hphysical⟩
      have hmateTerminal :
          canonicalPhysicalStrandPartner hdegree hallowed terminal =
            mateTerminal :=
        canonicalStrandPath_terminal_unique hpath
          (CanonicalStrandPathToPhysical.stop mateTerminal)
      apply terminal.1.localMate_ne_self
      exact congrArg Subtype.val (hmateTerminal.symm.trans hpartner)
  | .internal hinternal =>
      have hvertexNe := canonicalInternalStart_terminal_vertexIndex_ne
        hdegree hallowed terminal.1.localMate hinternal hpath
      apply hvertexNe
      calc
        (canonicalPhysicalStrandPartner
            hdegree hallowed terminal).1.vertexIndex =
            terminal.1.vertexIndex :=
          congrArg
            (fun occurrence : CanonicalPhysicalStrandPort
              external auxiliary hallowed => occurrence.1.vertexIndex)
            hpartner
        _ = terminal.1.localMate.vertexIndex :=
          (ResolvedNetworkPort.localMate_vertexIndex terminal.1).symm

/-! ## 5. The two paired terminals lie on different physical edges -/

/-- A one-element list has only one possible member. -/
private theorem eq_of_mem_of_length_eq_one
    {A : Type} [DecidableEq A] {entries : List A} {left right : A}
    (hlength : entries.length = 1)
    (hleft : left ∈ entries) (hright : right ∈ entries) :
    left = right := by
  cases entries with
  | nil => exact False.elim (List.not_mem_nil hleft)
  | cons head tail =>
      cases tail with
      | nil =>
          rcases List.mem_cons.mp hleft with hleftHead | hleftNil
          · rcases List.mem_cons.mp hright with hrightHead | hrightNil
            · exact hleftHead.trans hrightHead.symm
            · exact False.elim (List.not_mem_nil hrightNil)
          · exact False.elim (List.not_mem_nil hleftNil)
      | cons next rest =>
          simp only [List.length_cons] at hlength
          omega

/-- Two physical terminals over the same canonical physical identifier have
the same underlying half-edge.  This is the conceptual use of the exact
physical occurrence count one. -/
theorem canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (left right : CanonicalPhysicalStrandPort external auxiliary hallowed)
    (hedge : left.1.edgeId = right.1.edgeId) :
    resolvedNetworkPortHalfEdge left.1 =
      resolvedNetworkPortHalfEdge right.1 := by
  let network := canonicalLinkResolvedStrandNetwork
    degree external auxiliary hallowed
  let fiber := halfEdgesOnEdge network left.1.edgeId
  have hlength : fiber.length = 1 :=
    canonicalLinkResolved_halfEdgesOnEdge_length_physical
      hdegree hallowed left.2
  have hleft : resolvedNetworkPortHalfEdge left.1 ∈ fiber :=
    (mem_halfEdgesOnEdge_iff _ _).mpr rfl
  have hright : resolvedNetworkPortHalfEdge right.1 ∈ fiber :=
    (mem_halfEdgesOnEdge_iff _ _).mpr hedge.symm
  exact eq_of_mem_of_length_eq_one hlength hleft hright

/-- The local terminal pairing joins two genuinely different physical edge
identifiers.  Thus, after specialization to a lattice link, it joins two
different incident plaquette faces rather than merely two unequal proof
records or strand slots. -/
theorem canonicalPhysicalStrandPartner_edgeId_ne
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true)
    (terminal : CanonicalPhysicalStrandPort external auxiliary hallowed) :
    (canonicalPhysicalStrandPartner
        hdegree hallowed terminal).1.edgeId ≠ terminal.1.edgeId := by
  intro hedge
  have hhalfEdge := canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
    hdegree hallowed
    (canonicalPhysicalStrandPartner hdegree hallowed terminal)
    terminal hedge
  have hpath := canonicalPhysicalStrandPartner_path
    hdegree hallowed terminal
  match hclass : canonicalResolvedPortClassify
      hdegree hallowed terminal.1.localMate with
  | .physical hphysical =>
      let mateTerminal : CanonicalPhysicalStrandPort
          external auxiliary hallowed := ⟨terminal.1.localMate, hphysical⟩
      have hpartner :
          canonicalPhysicalStrandPartner hdegree hallowed terminal =
            mateTerminal :=
        canonicalStrandPath_terminal_unique hpath
          (CanonicalStrandPathToPhysical.stop mateTerminal)
      have hleg : terminal.1.localMate.leg = terminal.1.leg := by
        have := congrArg ResolvedNetworkHalfEdge.leg hhalfEdge
        simpa only [hpartner] using this
      exact terminal.1.localMate_leg_ne hleg
  | .internal hinternal =>
      have hvertexNe := canonicalInternalStart_terminal_vertexIndex_ne
        hdegree hallowed terminal.1.localMate hinternal hpath
      apply hvertexNe
      have hvertex := congrArg ResolvedNetworkHalfEdge.vertexIndex hhalfEdge
      exact hvertex.trans
        (ResolvedNetworkPort.localMate_vertexIndex terminal.1).symm

/-! ## 6. The data-bearing local pairing -/

/-- A data-bearing fixed-point-free involution on physical strand terminals. -/
structure CanonicalPhysicalStrandPairing
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) : Type where
  partner : CanonicalPhysicalStrandPort external auxiliary hallowed →
    CanonicalPhysicalStrandPort external auxiliary hallowed
  involutive : ∀ terminal, partner (partner terminal) = terminal
  ne_self : ∀ terminal, partner terminal ≠ terminal

/-- The canonical physical-terminal operation is a genuine pairing: it is
involutive and fixed-point-free. -/
def canonicalPhysicalStrandPairing
    {degree : Nat} {external auxiliary : EdgeLabelling}
    (hdegree : degree ≤ linkIncidenceBound)
    (hallowed :
      YMGap.Continuum.Z4FixedExternalLinkFusionMultiplicity.canonicalLinkConditionalAllowedB
        degree external auxiliary = true) :
    CanonicalPhysicalStrandPairing hallowed where
  partner := canonicalPhysicalStrandPartner hdegree hallowed
  involutive := canonicalPhysicalStrandPartner_involutive hdegree hallowed
  ne_self := canonicalPhysicalStrandPartner_ne_self hdegree hallowed

#print axioms canonicalOrientedInternalState_step_direction
#print axioms canonicalOrientedInternalState_current_lt_next_of_source_lt_current
#print axioms canonicalOrientedInternalState_next_lt_current_of_current_lt_source
#print axioms canonicalOrientedInternalState_path_terminal_beyond
#print axioms canonicalInternalStart_terminal_vertexIndex_ne
#print axioms canonicalPhysicalStrandPartner_ne_self
#print axioms canonicalPhysicalTerminals_halfEdge_eq_of_edgeId_eq
#print axioms canonicalPhysicalStrandPartner_edgeId_ne
#print axioms CanonicalPhysicalStrandPairing
#print axioms canonicalPhysicalStrandPairing

end YMGap.Continuum.CanonicalLinkPhysicalTerminalPairing
