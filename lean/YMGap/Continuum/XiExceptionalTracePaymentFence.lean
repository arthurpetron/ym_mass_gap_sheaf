/-
# Strict activity-loss fence for the sharp traced final carrier

The sharp fuel theorem places a normalized detour in the ordinary occurrence
carrier when its actual step count fits.  That does not provide the required
weight direction.  This closed three-occurrence example has one normalization
step, fits the exact `N + 1` vertex capacity, and has initial activity `1/64`
but final carrier weight `1/256` at the derived rational coupling `w = 1/2`.

Thus final-trace carrier membership and source-free injective bookkeeping do
not by themselves pay for normalization.  Any successful continuation must
supply an additional aggregate/fibre payment mechanism; pointwise replacement
by the final carrier is false.
-/

import YMGap.Continuum.XiExceptionalTraceFuelSharp

namespace YMGap.Continuum.XiExceptionalTracePaymentFence

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalTracedNormalization
open YMGap.Continuum.XiExceptionalTraceRightInvariant
open YMGap.Continuum.XiExceptionalTraceFuelSharp

local infix:50 " ≈ " => Q'.eqv

abbrev TL := toyLattice

instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def p : TL.Plaquette := (0, 0)
def X : Polymer TL := [p]
def Gamma : List (Polymer TL) := [X, X, X]
def labelOne : TL.Plaquette → Rep := fun _ => 1
def qAll : Polymer TL → Bool := fun _ => true
def bAll : Polymer TL → Bool := fun _ => true
def half : Q' := Q'.mkPos 1 2 (by decide)
def quarter : Q' := Q'.mkPos 1 4 (by decide)
def oneOver64 : Q' := Q'.mkPos 1 64 (by decide)
def oneOver256 : Q' := Q'.mkPos 1 256 (by decide)

def bits3 (x0 x1 x2 : Bool) : OccBitVec 3 :=
  .cons x0 (.cons x1 (.cons x2 .nil))

def directWalk : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (by rfl) (.single 1)

def initialState : SpliceState Gamma 0 1 :=
  { walk := directWalk
    residual := bits3 false false true }

theorem initialState_unsafe : initialState.unsafeCheckB = false := by
  rfl

theorem initialState_potential : initialState.potential = 1 := by
  rfl

theorem initialState_walk_length : initialState.walk.vertices.length = 2 := by
  rfl

theorem initialState_sharp_budget :
    initialState.walk.vertices.length + 2 * initialState.potential =
      Gamma.length + 1 := by
  rfl

theorem initialState_vertices_bound :
    ∀ k, k ∈ initialState.walk.vertices → k < Gamma.length := by
  intro k hk
  simp only [initialState, directWalk, CWalk.vertices, List.mem_cons,
    List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl <;> decide

def finalState : SpliceState Gamma 0 1 :=
  initialState.step initialState_unsafe

theorem finalState_safe : finalState.unsafeCheckB = true := by
  rfl

def witnessCode : EntryLeftTraceRightCode Gamma :=
  { traced :=
      { start := 0
        finish := 1
        trace := tracedExhaust initialState }
    rightResidual := bits3 false false false }

theorem witnessCode_trace_canonical :
    witnessCode.traced.trace =
      tracedExhaust witnessCode.traced.trace.decodeInitial := by
  unfold witnessCode
  dsimp only
  rw [tracedExhaust_decodeInitial]

theorem witnessCode_final_vertices_bound :
    ∀ k, k ∈ witnessCode.traced.trace.final.walk.vertices →
      k < Gamma.length := by
  exact tracedExhaust_final_vertices_bound initialState
    initialState_vertices_bound

theorem witnessCode_final_eq : witnessCode.traced.trace.final = finalState := by
  unfold witnessCode
  dsimp only
  rw [tracedExhaust]
  split
  next hunsafe =>
    change (tracedExhaust (initialState.step hunsafe)).final = finalState
    have hstep : initialState.step hunsafe = finalState := by
      unfold finalState
      rfl
    rw [hstep, tracedExhaust]
    split
    next hstillUnsafe =>
      rw [finalState_safe] at hstillUnsafe
      cases hstillUnsafe
    next _ => rfl
  next hsafe =>
    exact False.elim (hsafe initialState_unsafe)

/-- The detoured final walk really is present in the old finite carrier at
the sharp `steps ≤ N`, equivalently `vertices ≤ N+1`, capacity. -/
theorem witness_finalCarrier_mem :
    traceFinalCarrier witnessCode ∈ occurrenceCarrierXiCodes Gamma := by
  apply traceFinalCarrier_mem_of_initial_budget witnessCode
    witnessCode_trace_canonical (by decide)
    witnessCode_final_vertices_bound
  unfold witnessCode
  dsimp only
  rw [tracedExhaust_decodeInitial]
  exact Nat.le_of_eq initialState_sharp_budget

theorem fundamental_activity_quarter :
    activity half X labelOne ≈ quarter := by
  decide

theorem initial_totalActivity_exact :
    SpliceState.totalActivity half labelOne initialState ≈ oneOver64 := by
  decide

theorem final_totalActivity_exact :
    SpliceState.totalActivity half labelOne
      witnessCode.traced.trace.final ≈ oneOver256 := by
  rw [witnessCode_final_eq]
  unfold finalState
  decide

theorem finalCarrier_weight_exact :
    occurrenceCarrierXiCodeWeight half qAll bAll bAll Gamma labelOne
      (traceFinalCarrier witnessCode) ≈ oneOver256 := by
  unfold traceFinalCarrier
  rw [witnessCode_final_eq]
  unfold finalState witnessCode
  dsimp only
  decide

/-- The required pointwise domination direction is strictly false even
though the final carrier is a genuine member of the finite target. -/
theorem finalCarrier_does_not_dominate_initial :
    ¬ (SpliceState.totalActivity half labelOne initialState ≤
      occurrenceCarrierXiCodeWeight half qAll bAll bAll Gamma labelOne
        (traceFinalCarrier witnessCode)) := by
  intro hdom
  have h64le256 : oneOver64 ≤ oneOver256 :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv initial_totalActivity_exact)
      (Q'.le_trans' _ _ _ hdom (Q'.le_of_eqv finalCarrier_weight_exact))
  exact (by decide : ¬ (oneOver64 ≤ oneOver256)) h64le256

theorem traced_final_strictly_loses_activity :
    SpliceState.totalActivity half labelOne witnessCode.traced.trace.final <
      SpliceState.totalActivity half labelOne initialState := by
  exact YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv final_totalActivity_exact)
      (by decide : oneOver256 < oneOver64))
    (Q'.ge_of_eqv initial_totalActivity_exact)

#print axioms initialState_unsafe
#print axioms initialState_sharp_budget
#print axioms witnessCode_trace_canonical
#print axioms witnessCode_final_eq
#print axioms witness_finalCarrier_mem
#print axioms fundamental_activity_quarter
#print axioms initial_totalActivity_exact
#print axioms final_totalActivity_exact
#print axioms finalCarrier_weight_exact
#print axioms finalCarrier_does_not_dominate_initial
#print axioms traced_final_strictly_loses_activity

end YMGap.Continuum.XiExceptionalTracePaymentFence
