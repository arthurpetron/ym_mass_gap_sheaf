/-
# Reversible trace for first-conflict normalization

Each frame stores the factorized prefix and suffix around the conflict pivot,
the selected detour occurrence, and the cleared residual.  It does not store
the original state.  Rejoining the factors and restoring the one consumed bit
recovers that state constructively.  A terminating traced exhaust therefore
has a left-inverse decoder and is injective.
-/

import YMGap.Continuum.XiExceptionalFirstConflictActivity

namespace YMGap.Continuum.XiExceptionalTracedNormalization

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalUnsafeSideExclusion
open YMGap.Continuum.XiExceptionalFirstConflictDetour
open YMGap.Continuum.XiExceptionalFirstConflictSplice
open YMGap.Continuum.XiExceptionalEntryFirstConflictSplice
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalFirstConflictActivity

variable {L : Lattice} [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

/-! ## Restore exactly the consumed residual occurrence -/

def restoreResidualAt : {n : Nat} → OccBitVec n → Nat → OccBitVec n
  | 0, .nil, _ => .nil
  | _ + 1, .cons _ tail, 0 => .cons true tail
  | _ + 1, .cons head tail, i + 1 =>
      .cons head (restoreResidualAt tail i)

theorem restoreResidualAt_clearResidualAt :
    ∀ {n : Nat} (bits : OccBitVec n) (i : Nat), bits.at i = true →
      restoreResidualAt (clearResidualAt bits i) i = bits
  | 0, .nil, _, h => by cases h
  | _ + 1, .cons head tail, 0, h => by
      change head = true at h
      subst head
      rfl
  | _ + 1, .cons head tail, i + 1, h => by
      have ih := restoreResidualAt_clearResidualAt tail i h
      cases head <;>
        simp only [clearResidualAt, restoreResidualAt, ih]

/-! ## Minimal reversible one-step frame -/

structure ReversibleStepFrame (Gamma : List (Polymer L))
    (start finish : Nat) : Type where
  pivot : Nat
  detour : Nat
  pre : CWalk (incAtDistinct Gamma) start pivot
  suf : CWalk (incAtDistinct Gamma) pivot finish
  outEdge : incAtDistinct Gamma pivot detour = true
  inEdge : incAtDistinct Gamma detour pivot = true
  residualAfter : OccBitVec Gamma.length

def ReversibleStepFrame.source
    {Gamma : List (Polymer L)} {start finish : Nat}
    (frame : ReversibleStepFrame Gamma start finish) :
    SpliceState Gamma start finish :=
  { walk := frame.pre.append frame.suf
    residual := restoreResidualAt frame.residualAfter frame.detour }

def ReversibleStepFrame.target
    {Gamma : List (Polymer L)} {start finish : Nat}
    (frame : ReversibleStepFrame Gamma start finish) :
    SpliceState Gamma start finish :=
  { walk := CWalk.endpointDetour frame.pre frame.suf frame.detour
      frame.outEdge frame.inEdge
    residual := frame.residualAfter }

def ReversibleStepFrame.multiplier
    (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (frame : ReversibleStepFrame Gamma start finish) : Q' :=
  activity w (polyAt Gamma frame.pivot) label

def frameOfStep {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    ReversibleStepFrame Gamma start finish :=
  let u := state.selectedUnsafe
  let hu := state.selectedUnsafe_spec hunsafe
  let j := firstConflictIndex Gamma state.walk.vertices u
  let split := CWalk.firstConflictFactorization Gamma state.walk u hu.2.2
  let hconflict :=
    (firstConflictIndex_mem_and_conflict Gamma state.walk.vertices u hu.2.2).2
  let hout := incAtDistinct_of_symConflict_true Gamma j u hconflict
  let hin : incAtDistinct Gamma u j = true := by
    rw [← incAtDistinct_symm Gamma]
    exact hout
  { pivot := j
    detour := u
    pre := split.pre
    suf := split.suf
    outEdge := hout
    inEdge := hin
    residualAfter := clearResidualAt state.residual u }

theorem frameOfStep_source
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (frameOfStep state hunsafe).source = state := by
  let hu := state.selectedUnsafe_spec hunsafe
  let split := CWalk.firstConflictFactorization Gamma state.walk
    state.selectedUnsafe hu.2.2
  have hwalk : (frameOfStep state hunsafe).source.walk = state.walk := by
    change split.pre.append split.suf = state.walk
    exact split.rejoin
  have hresidual : (frameOfStep state hunsafe).source.residual =
      state.residual := by
    change restoreResidualAt
      (clearResidualAt state.residual state.selectedUnsafe)
        state.selectedUnsafe = state.residual
    exact restoreResidualAt_clearResidualAt state.residual
      state.selectedUnsafe hu.2.1
  calc
    (frameOfStep state hunsafe).source =
        { walk := state.walk
          residual := (frameOfStep state hunsafe).source.residual } :=
      congrArg (fun walk : CWalk (incAtDistinct Gamma) start finish =>
        ({ walk := walk
           residual := (frameOfStep state hunsafe).source.residual } :
          SpliceState Gamma start finish)) hwalk
    _ = { walk := state.walk, residual := state.residual } :=
      congrArg (fun residual : OccBitVec Gamma.length =>
        ({ walk := state.walk, residual := residual } :
          SpliceState Gamma start finish)) hresidual
    _ = state := by cases state; rfl

theorem frameOfStep_target
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    (frameOfStep state hunsafe).target = state.step hunsafe := by
  rfl

theorem frameOfStep_totalActivity_eqv
    (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish)
    (hunsafe : state.unsafeCheckB = false) :
    SpliceState.totalActivity w label (frameOfStep state hunsafe).target ≈
      SpliceState.totalActivity w label (frameOfStep state hunsafe).source *
        (frameOfStep state hunsafe).multiplier w label := by
  rw [frameOfStep_target, frameOfStep_source]
  exact SpliceState.step_totalActivity_eqv w label state hunsafe

theorem frameOfStep_injective
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state1 state2 : SpliceState Gamma start finish)
    (hunsafe1 : state1.unsafeCheckB = false)
    (hunsafe2 : state2.unsafeCheckB = false)
    (hframe : frameOfStep state1 hunsafe1 = frameOfStep state2 hunsafe2) :
    state1 = state2 := by
  have hsource := congrArg ReversibleStepFrame.source hframe
  rw [frameOfStep_source, frameOfStep_source] at hsource
  exact hsource

/-! ## Traced terminating normalization and its decoder -/

structure TracedNormalization (Gamma : List (Polymer L))
    (start finish : Nat) : Type where
  final : SpliceState Gamma start finish
  frames : List (ReversibleStepFrame Gamma start finish)

def TracedNormalization.decodeInitial
    {Gamma : List (Polymer L)} {start finish : Nat}
    (trace : TracedNormalization Gamma start finish) :
    SpliceState Gamma start finish :=
  match trace.frames with
  | [] => trace.final
  | frame :: _ => frame.source

def tracedExhaust {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    TracedNormalization Gamma start finish :=
  if hunsafe : state.unsafeCheckB = false then
    let tail := tracedExhaust (state.step hunsafe)
    { final := tail.final
      frames := frameOfStep state hunsafe :: tail.frames }
  else
    { final := state, frames := [] }
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem tracedExhaust_decodeInitial
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).decodeInitial = state := by
  rw [tracedExhaust]
  split
  next hunsafe =>
    exact frameOfStep_source state hunsafe
  next _ => rfl

theorem tracedExhaust_final_eq_exhaust
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).final = SpliceState.exhaust state := by
  rw [tracedExhaust, SpliceState.exhaust]
  split
  next hunsafe =>
    exact tracedExhaust_final_eq_exhaust (state.step hunsafe)
  next _ => rfl
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem tracedExhaust_final_safe
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    (tracedExhaust state).final.unsafeCheckB = true := by
  rw [tracedExhaust_final_eq_exhaust]
  exact SpliceState.exhaust_unsafeCheckB_true state

theorem tracedExhaust_injective
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state1 state2 : SpliceState Gamma start finish)
    (htrace : tracedExhaust state1 = tracedExhaust state2) :
    state1 = state2 := by
  have hdecoded := congrArg TracedNormalization.decodeInitial htrace
  rw [tracedExhaust_decodeInitial, tracedExhaust_decodeInitial] at hdecoded
  exact hdecoded

/-! ## Exact trace multiplier and strong-coupling monotonicity -/

def traceMultiplier (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat} :
    List (ReversibleStepFrame Gamma start finish) → Q'
  | [] => 1
  | frame :: frames =>
      frame.multiplier w label * traceMultiplier w label frames

theorem tracedExhaust_finalActivity_eqv
    (w : Q') (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    SpliceState.totalActivity w label (tracedExhaust state).final ≈
      SpliceState.totalActivity w label state *
        traceMultiplier w label (tracedExhaust state).frames := by
  rw [tracedExhaust]
  split
  next hunsafe =>
    have ih := tracedExhaust_finalActivity_eqv
      w label (state.step hunsafe)
    have hstep := SpliceState.step_totalActivity_eqv
      w label state hunsafe
    refine Q'.eqv_trans _ _ _ ih ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hstep) ?_
    change (SpliceState.totalActivity w label state *
        activity w (polyAt Gamma (firstConflictIndex Gamma
          state.walk.vertices state.selectedUnsafe)) label) *
          traceMultiplier w label
            (tracedExhaust (state.step hunsafe)).frames ≈
      SpliceState.totalActivity w label state *
        (activity w (polyAt Gamma (firstConflictIndex Gamma
          state.walk.vertices state.selectedUnsafe)) label *
            traceMultiplier w label
              (tracedExhaust (state.step hunsafe)).frames)
    ring_qeqv
  next _ =>
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
termination_by state.potential
decreasing_by apply SpliceState.step_potential_lt

theorem tracedExhaust_finalActivity_le_of_strong
    {w : Q'} (hw0 : (0 : Q') ≤ w)
    (hw : w ≤ Q'.mkPos 1 2 (by decide))
    (label : L.Plaquette → Rep)
    {Gamma : List (Polymer L)} {start finish : Nat}
    (state : SpliceState Gamma start finish) :
    SpliceState.totalActivity w label (tracedExhaust state).final ≤
      SpliceState.totalActivity w label state := by
  rw [tracedExhaust_final_eq_exhaust]
  exact SpliceState.exhaust_totalActivity_le_of_strong hw0 hw label state

#print axioms restoreResidualAt_clearResidualAt
#print axioms frameOfStep_source
#print axioms frameOfStep_target
#print axioms frameOfStep_totalActivity_eqv
#print axioms frameOfStep_injective
#print axioms tracedExhaust
#print axioms tracedExhaust_decodeInitial
#print axioms tracedExhaust_final_eq_exhaust
#print axioms tracedExhaust_final_safe
#print axioms tracedExhaust_injective
#print axioms tracedExhaust_finalActivity_eqv
#print axioms tracedExhaust_finalActivity_le_of_strong

end YMGap.Continuum.XiExceptionalTracedNormalization
