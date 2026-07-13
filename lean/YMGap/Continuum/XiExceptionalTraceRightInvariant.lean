/-
# Trace-only collision and the missing right-residual invariant

The reversible normalization trace recovers its initial splice state, hence
the conflict walk and the cleared left residual.  It does not record the
cleared right residual.  This file isolates that loss of information and
adds exactly the missing occurrence mask, without retaining the exceptional
source entry itself.

The resulting trace-plus-right code reconstructs the already existing
two-sided original carrier code.  This is a structural compression theorem,
not a weighted domination theorem: for an unsafe left residual, the old
carrier still has no proved activity payment.
-/

import YMGap.Continuum.XiExceptionalTracedUnsafeAdapter
import YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

namespace YMGap.Continuum.XiExceptionalTraceRightInvariant

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalBranchPacking
open YMGap.Continuum.XiExceptionalCustomCarrier
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalParallelResidualBlock
open YMGap.Continuum.XiExceptionalOneAttachedResidualConsumer
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalTracedNormalization
open YMGap.Continuum.XiExceptionalTracedUnsafeAdapter
open YMGap.Continuum.XiExceptionalTwoSidedOriginalCarrier

variable {L : Lattice} [DecidableEq L.Plaquette]

/-! ## Source-free trace packages -/

/-- The normalization trace with its dependent endpoints packaged as data.
Unlike `EntryTracedCode`, this structure does not retain the source entry. -/
structure EntryLeftTraceCode (Gamma : List (Polymer L)) : Type where
  start : Nat
  finish : Nat
  trace : TracedNormalization Gamma start finish

/-- The trace together with the occurrence mask which the initial splice
state omits: the original right side, cleared on the canonical path. -/
structure EntryLeftTraceRightCode (Gamma : List (Polymer L)) : Type where
  traced : EntryLeftTraceCode Gamma
  rightResidual : OccBitVec Gamma.length

def entryLeftTraceCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    EntryLeftTraceCode Gamma := by
  let facts := exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2
  let path := sourceExceptionalPath Gamma qP b1 b2 entry.1 facts
  exact
    { start := exceptionalMarkedIndex Gamma b1 b2 entry.1
      finish := path.seed
      trace := tracedExhaust (entryLeftSpliceState Gamma qP b1 b2 entry) }

def entryLeftTraceRightCode
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    EntryLeftTraceRightCode Gamma :=
  { traced := entryLeftTraceCode Gamma qP b1 b2 entry
    rightResidual := rightPathResidual Gamma qP b1 b2 entry }

/-- Transport only the two endpoint indices of a splice state. -/
def castSpliceStateEndpoints {Gamma : List (Polymer L)}
    {start finish start' finish' : Nat}
    (hstart : start = start') (hfinish : finish = finish')
    (state : SpliceState Gamma start finish) :
    SpliceState Gamma start' finish' := by
  subst start'
  subst finish'
  exact state

/-- The corresponding endpoint transport for a walk. -/
def castCWalkEndpoints {edge : Nat → Nat → Bool}
    {start finish start' finish' : Nat}
    (hstart : start = start') (hfinish : finish = finish')
    (walk : CWalk edge start finish) : CWalk edge start' finish' := by
  subst start'
  subst finish'
  exact walk

@[simp] theorem castCWalkEndpoints_vertices
    {edge : Nat → Nat → Bool}
    {start finish start' finish' : Nat}
    (hstart : start = start') (hfinish : finish = finish')
    (walk : CWalk edge start finish) :
    (castCWalkEndpoints hstart hfinish walk).vertices = walk.vertices := by
  subst start'
  subst finish'
  rfl

@[simp] theorem castSpliceStateEndpoints_walk
    {Gamma : List (Polymer L)} {start finish start' finish' : Nat}
    (hstart : start = start') (hfinish : finish = finish')
    (state : SpliceState Gamma start finish) :
    (castSpliceStateEndpoints hstart hfinish state).walk =
      castCWalkEndpoints hstart hfinish state.walk := by
  subst start'
  subst finish'
  rfl

@[simp] theorem castSpliceStateEndpoints_residual
    {Gamma : List (Polymer L)} {start finish start' finish' : Nat}
    (hstart : start = start') (hfinish : finish = finish')
    (state : SpliceState Gamma start finish) :
    (castSpliceStateEndpoints hstart hfinish state).residual = state.residual := by
  subst start'
  subst finish'
  rfl

theorem entryLeftTraceCode_castEndpoints
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2)
    (start finish : Nat)
    (hstart : exceptionalMarkedIndex Gamma b1 b2 entry.1 = start)
    (hfinish :
      (sourceExceptionalPath Gamma qP b1 b2 entry.1
        (exceptionalSourceFactsOfMem Gamma qP b1 b2 entry.1 entry.2)).seed =
          finish) :
    entryLeftTraceCode Gamma qP b1 b2 entry =
      { start := start
        finish := finish
        trace := tracedExhaust
          (castSpliceStateEndpoints hstart hfinish
            (entryLeftSpliceState Gamma qP b1 b2 entry)) } := by
  subst start
  subst finish
  rfl

theorem spliceState_eq_of_fields
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state1 state2 : SpliceState Gamma start finish)
    (hwalk : state1.walk = state2.walk)
    (hresidual : state1.residual = state2.residual) :
    state1 = state2 := by
  cases state1 with
  | mk walk1 residual1 =>
      cases state2 with
      | mk walk2 residual2 =>
          cases hwalk
          cases hresidual
          rfl

/-- Forget normalization history and turn the decoded initial state plus the
right residual into an ordinary occurrence-carrier datum. -/
def EntryLeftTraceRightCode.initialCarrier
    {Gamma : List (Polymer L)} (code : EntryLeftTraceRightCode Gamma) :
    OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := code.traced.start
        chain := occurrenceChainCodeOfWalk
          code.traced.trace.decodeInitial.walk
          code.traced.trace.decodeInitial.residual }
    external := code.rightResidual }

/-! ## The trace walk has the same occurrence-chain syntax -/

theorem occurrenceChainCodeOfWalk_map_id
    {edgeA edgeB : Nat → Nat → Bool}
    (hedge : ∀ x y, edgeA x y = true → edgeB x y = true) :
    ∀ {i j : Nat} (walk : CWalk edgeA i j) (background : OccBitVec n),
      occurrenceChainCodeOfWalk (mapCWalk id hedge walk) background =
        occurrenceChainCodeOfWalk walk background
  | _, _, .single _, _ => rfl
  | _, _, .cons _ rest, background => by
      simp only [mapCWalk, occurrenceChainCodeOfWalk, CWalk.start_eq]
      simpa only [id_eq] using congrArg (OccChainCode.step rest.start)
        (occurrenceChainCodeOfWalk_map_id hedge rest background)

theorem occurrenceChainCodeOfWalk_conflictWalk
    (Gamma : List (Polymer L)) (left right : Nat → Bool) {i j : Nat}
    (walk : CWalk
      (disagreementEdge Gamma.length (incAtDistinct Gamma) left right)
      i j)
    (background : OccBitVec Gamma.length) :
    occurrenceChainCodeOfWalk
        (conflictWalkOfDisagreement Gamma left right walk) background =
      occurrenceChainCodeOfWalk walk background := by
  unfold conflictWalkOfDisagreement
  apply occurrenceChainCodeOfWalk_map_id

/-! ## Reconstruction and injectivity after adding the missing invariant -/

theorem entryLeftTraceRight_initialCarrier
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryLeftTraceRightCode Gamma qP b1 b2 entry).initialCarrier =
      originalTwoSidedCarrierCode Gamma qP b1 b2 entry := by
  rw [EntryLeftTraceRightCode.initialCarrier]
  simp only [entryLeftTraceRightCode, entryLeftTraceCode]
  rw [tracedExhaust_decodeInitial]
  unfold entryLeftSpliceState originalTwoSidedCarrierCode
    exceptionalCustomCarrierCode
  simp only [id_eq]
  rw [occurrenceChainCodeOfWalk_conflictWalk]

theorem entryLeftTraceRight_initialCarrier_mem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry : ExceptionalSourceEntry Gamma qP b1 b2) :
    (entryLeftTraceRightCode Gamma qP b1 b2 entry).initialCarrier ∈
      occurrenceCarrierXiCodes Gamma := by
  rw [entryLeftTraceRight_initialCarrier]
  exact originalTwoSidedCarrierCode_mem Gamma qP b1 b2 entry

theorem entryLeftTraceRightCode_injective
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (entry1 entry2 : ExceptionalSourceEntry Gamma qP b1 b2)
    (hcode : entryLeftTraceRightCode Gamma qP b1 b2 entry1 =
      entryLeftTraceRightCode Gamma qP b1 b2 entry2) :
    entry1 = entry2 := by
  have hcarrier := congrArg EntryLeftTraceRightCode.initialCarrier hcode
  rw [entryLeftTraceRight_initialCarrier,
    entryLeftTraceRight_initialCarrier] at hcarrier
  exact originalTwoSidedCarrierCode_injective
    Gamma qP b1 b2 entry1 entry2 hcarrier

/-! ## A closed collision: trace alone forgets an off-path right branch -/

namespace TraceOnlyCollision

abbrev TL := toyLattice

instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def p0 : TL.Plaquette := (0, 0)
def p1 : TL.Plaquette := (1, 0)
def A : Polymer TL := [p0]
def B : Polymer TL := [p0, p1]
def C : Polymer TL := [p1]
def Gamma : List (Polymer TL) := [A, B, C]
def qAll : Polymer TL → Bool := fun _ => true
def markA : Polymer TL → Bool := fun X => decide (X = A)
def badB : Polymer TL → Bool := fun X => decide (X = B)

def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

def pairBare : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false false)

def pairBranch : MaskPair Gamma.length :=
  (bits3 false true false, bits3 true false true)

theorem pairBare_mem :
    pairBare ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBare, ?_⟩
  rfl

theorem pairBranch_mem :
    pairBranch ∈ exceptionalSourceCodes Gamma qAll markA badB := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pairBranch, ?_⟩
  rfl

def entryBare : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBare, pairBare_mem⟩

def entryBranch : ExceptionalSourceEntry Gamma qAll markA badB :=
  ⟨pairBranch, pairBranch_mem⟩

theorem entries_ne : entryBare ≠ entryBranch := by
  intro h
  have hp : pairBare = pairBranch := congrArg Subtype.val h
  have hbit := congrArg (fun pair => pair.2.at 2) hp
  cases hbit

private theorem CWalk.end_mem_vertices
    {alpha : Type} {edge : alpha → alpha → Bool} :
    ∀ {x y : alpha} (walk : CWalk edge x y), y ∈ walk.vertices
  | _, _, .single _ => List.mem_cons_self
  | _, _, .cons _ rest =>
      List.mem_cons_of_mem _ (CWalk.end_mem_vertices rest)

private theorem direct_walk_vertices
    {edge : Nat → Nat → Bool} {start finish : Nat}
    (walk : CWalk edge start finish)
    (hstart : start = 0) (hfinish : finish = 1)
    (hnodup : walk.vertices.Nodup)
    (hfirst : ∀ j, edge 0 j = true → j = 1) :
    walk.vertices = [0, 1] := by
  subst start
  subst finish
  cases walk with
  | @cons _ next _ hedge rest =>
      have hnext := hfirst next hedge
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next2 _ hedge2 tail =>
          have hp := List.nodup_cons.mp hnodup
          have htail := List.nodup_cons.mp hp.2
          exact absurd (CWalk.end_mem_vertices tail) htail.1

private theorem CWalk.eq_direct_of_vertices
    {edge : Nat → Nat → Bool}
    (walk : CWalk edge 0 1) (hedge : edge 0 1 = true)
    (hvertices : walk.vertices = [0, 1]) :
    walk = .cons hedge (.single 1) := by
  cases walk with
  | @cons _ next _ hfirst rest =>
      have htailVertices : rest.vertices = [1] := by
        injection hvertices
      have hnext : next = 1 := by
        exact List.mem_singleton.mp (by
          rw [← htailVertices]
          exact CWalk.start_mem_vertices rest)
      subst next
      cases rest with
      | single _ => rfl
      | @cons _ next2 _ hedge2 tail =>
          have hempty : tail.vertices = [] := by
            simp only [CWalk.vertices] at htailVertices
            injection htailVertices
          exact absurd (CWalk.end_mem_vertices tail) (by
            rw [hempty]
            exact List.not_mem_nil)

private theorem badB_polyAt_index {i : Nat} (hi : i < Gamma.length)
    (hbad : badB (polyAt Gamma i) = true) : i = 1 := by
  have hi3 : i < 3 := by simpa [Gamma] using hi
  have hne0 : i ≠ 0 := by
    intro h
    subst i
    cases hbad
  have hne2 : i ≠ 2 := by
    intro h
    subst i
    cases hbad
  omega

private theorem bare_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB
      pairBare pairBare_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pairBare facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB
    pairBare pairBare_mem
  let path := sourceExceptionalPath Gamma qAll markA badB pairBare facts
  have hstart : exceptionalMarkedIndex Gamma markA badB pairBare = 0 := by
    rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairBare.1) (bitMask pairBare.2) (predAt Gamma badB)
    path.seed_true
  have hfinish : path.seed = 1 := badB_polyAt_index hp.1 hp.2.2.2
  apply direct_walk_vertices path.indexWalk hstart hfinish path.index_nodup
  intro j hedge
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pairBare.1) (bitMask pairBare.2) hedge).2
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have hj0 : j ≠ 0 := by intro h; subst j; cases hedge
  have hj2 : j ≠ 2 := by intro h; subst j; cases hedge
  omega

private theorem branch_path_vertices :
    let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB
      pairBranch pairBranch_mem
    let path := sourceExceptionalPath Gamma qAll markA badB pairBranch facts
    path.indexWalk.vertices = [0, 1] := by
  dsimp only
  let facts := exceptionalSourceFactsOfMem Gamma qAll markA badB
    pairBranch pairBranch_mem
  let path := sourceExceptionalPath Gamma qAll markA badB pairBranch facts
  have hstart : exceptionalMarkedIndex Gamma markA badB pairBranch = 0 := by
    rfl
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairBranch.1) (bitMask pairBranch.2) (predAt Gamma badB)
    path.seed_true
  have hfinish : path.seed = 1 := badB_polyAt_index hp.1 hp.2.2.2
  apply direct_walk_vertices path.indexWalk hstart hfinish path.index_nodup
  intro j hedge
  have hj := (disagreementEdge_bounds Gamma.length (incAtDistinct Gamma)
    (bitMask pairBranch.1) (bitMask pairBranch.2) hedge).2
  have hj3 : j < 3 := by simpa [Gamma] using hj
  have hj0 : j ≠ 0 := by intro h; subst j; cases hedge
  have hj2 : j ≠ 2 := by intro h; subst j; cases hedge
  omega

private theorem bare_seed_eq_one :
    (sourceExceptionalPath Gamma qAll markA badB pairBare
      (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBare
        pairBare_mem)).seed = 1 := by
  let path := sourceExceptionalPath Gamma qAll markA badB pairBare
    (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBare pairBare_mem)
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairBare.1) (bitMask pairBare.2) (predAt Gamma badB)
    path.seed_true
  exact badB_polyAt_index hp.1 hp.2.2.2

private theorem branch_seed_eq_one :
    (sourceExceptionalPath Gamma qAll markA badB pairBranch
      (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBranch
        pairBranch_mem)).seed = 1 := by
  let path := sourceExceptionalPath Gamma qAll markA badB pairBranch
    (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBranch pairBranch_mem)
  have hp := forwardSeed_parts Gamma.length
    (bitMask pairBranch.1) (bitMask pairBranch.2) (predAt Gamma badB)
    path.seed_true
  exact badB_polyAt_index hp.1 hp.2.2.2

private theorem bare_left_residual_empty :
    leftPathResidual Gamma qAll markA badB entryBare =
      bits3 false false false := by
  unfold leftPathResidual entryBare
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pairBare
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBare
          pairBare_mem)).indexWalk.vertices)
    pairBare.1 = bits3 false false false
  rw [bare_path_vertices]
  rfl

private theorem branch_left_residual_empty :
    leftPathResidual Gamma qAll markA badB entryBranch =
      bits3 false false false := by
  unfold leftPathResidual entryBranch
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pairBranch
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBranch
          pairBranch_mem)).indexWalk.vertices)
    pairBranch.1 = bits3 false false false
  rw [branch_path_vertices]
  rfl

private def bareInitialState : SpliceState Gamma 0 1 :=
  castSpliceStateEndpoints (by rfl) bare_seed_eq_one
    (entryLeftSpliceState Gamma qAll markA badB entryBare)

private def branchInitialState : SpliceState Gamma 0 1 :=
  castSpliceStateEndpoints (by rfl) branch_seed_eq_one
    (entryLeftSpliceState Gamma qAll markA badB entryBranch)

private theorem bareInitialState_vertices :
    bareInitialState.walk.vertices = [0, 1] := by
  unfold bareInitialState
  rw [castSpliceStateEndpoints_walk, castCWalkEndpoints_vertices]
  unfold entryLeftSpliceState
  simp only [id_eq]
  simp only [entryBare]
  rw [conflictWalkOfDisagreement_vertices]
  exact bare_path_vertices

private theorem branchInitialState_vertices :
    branchInitialState.walk.vertices = [0, 1] := by
  unfold branchInitialState
  rw [castSpliceStateEndpoints_walk, castCWalkEndpoints_vertices]
  unfold entryLeftSpliceState
  simp only [id_eq]
  simp only [entryBranch]
  rw [conflictWalkOfDisagreement_vertices]
  exact branch_path_vertices

private theorem initialStates_collision :
    bareInitialState = branchInitialState := by
  have hwalk : bareInitialState.walk = branchInitialState.walk := by
    have hbare := CWalk.eq_direct_of_vertices bareInitialState.walk
      (show incAtDistinct Gamma 0 1 = true by rfl)
      bareInitialState_vertices
    have hbranch := CWalk.eq_direct_of_vertices branchInitialState.walk
      (show incAtDistinct Gamma 0 1 = true by rfl)
      branchInitialState_vertices
    exact hbare.trans hbranch.symm
  have hresidual : bareInitialState.residual =
      branchInitialState.residual := by
    unfold bareInitialState branchInitialState
    rw [castSpliceStateEndpoints_residual,
      castSpliceStateEndpoints_residual]
    exact bare_left_residual_empty.trans branch_left_residual_empty.symm
  exact spliceState_eq_of_fields bareInitialState branchInitialState
    hwalk hresidual

set_option maxHeartbeats 1000000 in
theorem trace_only_collision :
    entryLeftTraceCode Gamma qAll markA badB entryBare =
      entryLeftTraceCode Gamma qAll markA badB entryBranch := by
  rw [entryLeftTraceCode_castEndpoints Gamma qAll markA badB entryBare
      0 1 (by rfl) bare_seed_eq_one,
    entryLeftTraceCode_castEndpoints Gamma qAll markA badB entryBranch
      0 1 (by rfl) branch_seed_eq_one]
  exact congrArg (fun state : SpliceState Gamma 0 1 =>
    EntryLeftTraceCode.mk 0 1 (tracedExhaust state))
    initialStates_collision

theorem no_trace_only_decoder
    (decode : EntryLeftTraceCode Gamma →
      ExceptionalSourceEntry Gamma qAll markA badB) :
    ¬ (decode (entryLeftTraceCode Gamma qAll markA badB entryBare) =
          entryBare ∧
        decode (entryLeftTraceCode Gamma qAll markA badB entryBranch) =
          entryBranch) := by
  intro hrecovers
  apply entries_ne
  exact hrecovers.1.symm.trans
    ((congrArg decode trace_only_collision).trans hrecovers.2)

theorem bare_right_residual_empty :
    rightPathResidual Gamma qAll markA badB entryBare =
      bits3 false false false := by
  unfold rightPathResidual entryBare
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pairBare
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBare
          pairBare_mem)).indexWalk.vertices)
    pairBare.2 = bits3 false false false
  rw [bare_path_vertices]
  rfl

theorem branch_right_residual_exact :
    rightPathResidual Gamma qAll markA badB entryBranch =
      bits3 false false true := by
  unfold rightPathResidual entryBranch
  change residualBits
    (pathOccurrenceBits Gamma.length
      (sourceExceptionalPath Gamma qAll markA badB pairBranch
        (exceptionalSourceFactsOfMem Gamma qAll markA badB pairBranch
          pairBranch_mem)).indexWalk.vertices)
    pairBranch.2 = bits3 false false true
  rw [branch_path_vertices]
  rfl

theorem right_residual_separates_collision :
    rightPathResidual Gamma qAll markA badB entryBare ≠
      rightPathResidual Gamma qAll markA badB entryBranch := by
  intro hresidual
  rw [bare_right_residual_empty, branch_right_residual_exact] at hresidual
  have hbit := congrArg (fun residual => residual.at 2) hresidual
  cases hbit

theorem trace_right_code_separates_collision :
    entryLeftTraceRightCode Gamma qAll markA badB entryBare ≠
      entryLeftTraceRightCode Gamma qAll markA badB entryBranch := by
  intro hcode
  exact entries_ne (entryLeftTraceRightCode_injective
    Gamma qAll markA badB entryBare entryBranch hcode)

end TraceOnlyCollision

#print axioms occurrenceChainCodeOfWalk_map_id
#print axioms occurrenceChainCodeOfWalk_conflictWalk
#print axioms entryLeftTraceCode_castEndpoints
#print axioms spliceState_eq_of_fields
#print axioms entryLeftTraceRight_initialCarrier
#print axioms entryLeftTraceRight_initialCarrier_mem
#print axioms entryLeftTraceRightCode_injective
#print axioms TraceOnlyCollision.pairBare_mem
#print axioms TraceOnlyCollision.pairBranch_mem
#print axioms TraceOnlyCollision.entries_ne
#print axioms TraceOnlyCollision.trace_only_collision
#print axioms TraceOnlyCollision.no_trace_only_decoder
#print axioms TraceOnlyCollision.bare_right_residual_empty
#print axioms TraceOnlyCollision.branch_right_residual_exact
#print axioms TraceOnlyCollision.right_residual_separates_collision
#print axioms TraceOnlyCollision.trace_right_code_separates_collision

end YMGap.Continuum.XiExceptionalTraceRightInvariant
