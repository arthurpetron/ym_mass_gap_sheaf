/-
# A finite final-carrier fibre paid by distinct occurrence multiplicity

The pointwise final-carrier map loses a factor in the three-occurrence fence.
Here the unabsorbed state and its already-absorbed final state are grouped in
one final-carrier fibre.  At `w = 1/2` their exact total activity is `5/256`.

The occurrence-indexed target has enough real (not duplicated-list) capacity
to pay this toy fibre: five distinct length-four walks on the three duplicate
occurrences each have weight `1/256`.  Their duplicate-free block therefore
has exactly the fibre weight.  This is a concrete aggregate mechanism, not a
global exceptional-source theorem.
-/

import YMGap.Continuum.XiExceptionalTracePaymentFence

namespace YMGap.Continuum.XiExceptionalFinalCarrierFiberBlock

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiExceptionalWeightedInjection
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalFirstConflictActivity
open YMGap.Continuum.XiExceptionalFirstConflictPotential
open YMGap.Continuum.XiExceptionalTracedNormalization
open YMGap.Continuum.XiExceptionalTraceRightInvariant
open YMGap.Continuum.XiExceptionalTraceFuelSharp
open YMGap.Continuum.XiExceptionalTracePaymentFence

local infix:50 " ≈ " => Q'.eqv

/-! ## The two-state fibre over one final carrier -/

def absorbedCode : EntryLeftTraceRightCode Gamma :=
  { traced :=
      { start := 0
        finish := 1
        trace := tracedExhaust finalState }
    rightResidual := bits3 false false false }

theorem absorbedCode_final_eq : absorbedCode.traced.trace.final = finalState := by
  unfold absorbedCode
  dsimp only
  rw [tracedExhaust]
  split
  next hunsafe =>
    rw [finalState_safe] at hunsafe
    cases hunsafe
  next _ => rfl

theorem fibre_finalCarrier_collision :
    traceFinalCarrier witnessCode = traceFinalCarrier absorbedCode := by
  unfold traceFinalCarrier
  rw [witnessCode_final_eq, absorbedCode_final_eq]
  unfold witnessCode absorbedCode
  rfl

def fibreStateWeight (state : SpliceState Gamma 0 1) : Q' :=
  SpliceState.totalActivity half labelOne state

def twoStateFibre : List (SpliceState Gamma 0 1) :=
  [initialState, finalState]

theorem finalState_totalActivity_exact :
    SpliceState.totalActivity half labelOne finalState ≈ oneOver256 := by
  rw [← witnessCode_final_eq]
  exact final_totalActivity_exact

theorem twoStateFibre_weight_exact :
    qListSum fibreStateWeight twoStateFibre ≈ Q'.mkPos 5 256 (by decide) := by
  simp only [twoStateFibre, qListSum_cons, qListSum_nil, fibreStateWeight]
  refine Q'.eqv_trans _
    (oneOver64 + (oneOver256 + 0)) _ ?_ ?_
  · exact Q'.add_eqv_congr' initial_totalActivity_exact
      (Q'.add_eqv_congr' finalState_totalActivity_exact (Q'.eqv_refl _))
  · decide

theorem twoStateFibre_is_one_finalCarrier_fibre :
    [traceFinalCarrier witnessCode, traceFinalCarrier absorbedCode] =
      [traceFinalCarrier witnessCode, traceFinalCarrier witnessCode] := by
  rw [fibre_finalCarrier_collision]

/-! ## Five distinct ordinary carriers of the required weight -/

def walk0101 : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (y := 1) (by rfl)
    (.cons (y := 0) (by rfl) (.cons (y := 1) (by rfl) (.single 1)))

def walk0201 : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (y := 2) (by rfl)
    (.cons (y := 0) (by rfl) (.cons (y := 1) (by rfl) (.single 1)))

def walk0120 : CWalk (incAtDistinct Gamma) 0 0 :=
  .cons (y := 1) (by rfl)
    (.cons (y := 2) (by rfl) (.cons (y := 0) (by rfl) (.single 0)))

def walk0210 : CWalk (incAtDistinct Gamma) 0 0 :=
  .cons (y := 2) (by rfl)
    (.cons (y := 1) (by rfl) (.cons (y := 0) (by rfl) (.single 0)))

def walk0121 : CWalk (incAtDistinct Gamma) 0 1 :=
  .cons (y := 1) (by rfl)
    (.cons (y := 2) (by rfl) (.cons (y := 1) (by rfl) (.single 1)))

def carrierOfWalk {finish : Nat}
    (walk : CWalk (incAtDistinct Gamma) 0 finish) : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk walk (bits3 false false false) }
    external := bits3 false false false }

def carrier0101 := carrierOfWalk walk0101
def carrier0201 := carrierOfWalk walk0201
def carrier0120 := carrierOfWalk walk0120
def carrier0210 := carrierOfWalk walk0210
def carrier0121 := carrierOfWalk walk0121

def fiveCarrierBlock : List (OccCarrierXiCodeAt Gamma) :=
  [carrier0101, carrier0201, carrier0120, carrier0210, carrier0121]

theorem walk0101_vertices : walk0101.vertices = [0, 1, 0, 1] := rfl
theorem walk0201_vertices : walk0201.vertices = [0, 2, 0, 1] := rfl
theorem walk0120_vertices : walk0120.vertices = [0, 1, 2, 0] := rfl
theorem walk0210_vertices : walk0210.vertices = [0, 2, 1, 0] := rfl
theorem walk0121_vertices : walk0121.vertices = [0, 1, 2, 1] := rfl

theorem fiveCarrierBlock_nodup : fiveCarrierBlock.Nodup := by
  decide

theorem carrierOfWalk_mem {finish : Nat}
    (walk : CWalk (incAtDistinct Gamma) 0 finish)
    (hlength : walk.vertices.length ≤ Gamma.length + 1)
    (hbounds : ∀ k, k ∈ walk.vertices → k < Gamma.length) :
    carrierOfWalk walk ∈ occurrenceCarrierXiCodes Gamma := by
  unfold carrierOfWalk occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨bits3 false false false,
    bitVectors_complete (bits3 false false false), ?_⟩
  apply List.mem_map.mpr
  refine ⟨(carrierOfWalk walk).carrier, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by decide), ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk walk (bits3 false false false), ?_, rfl⟩
  exact occurrenceChainCodeOfWalk_mem_sharp Gamma
    (bits3 false false false) walk Gamma.length hlength hbounds

private theorem closed_walk_bounds (vertices : List Nat)
    (hvertices : vertices = [0, 1, 0, 1] ∨
      vertices = [0, 2, 0, 1] ∨
      vertices = [0, 1, 2, 0] ∨
      vertices = [0, 2, 1, 0] ∨
      vertices = [0, 1, 2, 1]) :
    ∀ k, k ∈ vertices → k < Gamma.length := by
  intro k hk
  rcases hvertices with h | h | h | h | h <;> rw [h] at hk <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk <;>
    rcases hk with rfl | rfl | rfl | rfl <;> decide

theorem carrier0101_mem : carrier0101 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0101
  · rw [walk0101_vertices]
    decide
  · exact closed_walk_bounds walk0101.vertices (Or.inl walk0101_vertices)

theorem carrier0201_mem : carrier0201 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0201
  · rw [walk0201_vertices]
    decide
  · exact closed_walk_bounds walk0201.vertices
      (Or.inr (Or.inl walk0201_vertices))

theorem carrier0120_mem : carrier0120 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0120
  · rw [walk0120_vertices]
    decide
  · exact closed_walk_bounds walk0120.vertices
      (Or.inr (Or.inr (Or.inl walk0120_vertices)))

theorem carrier0210_mem : carrier0210 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0210
  · rw [walk0210_vertices]
    decide
  · exact closed_walk_bounds walk0210.vertices
      (Or.inr (Or.inr (Or.inr (Or.inl walk0210_vertices))))

theorem carrier0121_mem : carrier0121 ∈ occurrenceCarrierXiCodes Gamma := by
  apply carrierOfWalk_mem walk0121
  · rw [walk0121_vertices]
    decide
  · exact closed_walk_bounds walk0121.vertices
      (Or.inr (Or.inr (Or.inr (Or.inr walk0121_vertices))))

def targetWeight (code : OccCarrierXiCodeAt Gamma) : Q' :=
  occurrenceCarrierXiCodeWeight half qAll bAll bAll Gamma labelOne code

theorem carrier0101_weight : targetWeight carrier0101 ≈ oneOver256 := by decide
theorem carrier0201_weight : targetWeight carrier0201 ≈ oneOver256 := by decide
theorem carrier0120_weight : targetWeight carrier0120 ≈ oneOver256 := by decide
theorem carrier0210_weight : targetWeight carrier0210 ≈ oneOver256 := by decide
theorem carrier0121_weight : targetWeight carrier0121 ≈ oneOver256 := by decide

theorem fiveCarrierBlock_weight_exact :
    qListSum targetWeight fiveCarrierBlock ≈ Q'.mkPos 5 256 (by decide) := by
  simp only [fiveCarrierBlock, qListSum_cons, qListSum_nil]
  refine Q'.eqv_trans _
    (oneOver256 + (oneOver256 + (oneOver256 +
      (oneOver256 + (oneOver256 + 0))))) _ ?_ ?_
  · exact Q'.add_eqv_congr' carrier0101_weight
      (Q'.add_eqv_congr' carrier0201_weight
        (Q'.add_eqv_congr' carrier0120_weight
          (Q'.add_eqv_congr' carrier0210_weight
            (Q'.add_eqv_congr' carrier0121_weight (Q'.eqv_refl _)))))
  · decide

/-- Exact toy aggregate payment: one two-state final-carrier fibre is paid by
a duplicate-free block of five genuine old-carrier codes. -/
theorem twoStateFibre_eqv_fiveCarrierBlock :
    qListSum fibreStateWeight twoStateFibre ≈
      qListSum targetWeight fiveCarrierBlock :=
  Q'.eqv_trans _ _ _ twoStateFibre_weight_exact
    (Q'.eqv_symm fiveCarrierBlock_weight_exact)

#print axioms absorbedCode_final_eq
#print axioms fibre_finalCarrier_collision
#print axioms twoStateFibre_weight_exact
#print axioms fiveCarrierBlock_nodup
#print axioms carrier0101_mem
#print axioms carrier0201_mem
#print axioms carrier0120_mem
#print axioms carrier0210_mem
#print axioms carrier0121_mem
#print axioms fiveCarrierBlock_weight_exact
#print axioms twoStateFibre_eqv_fiveCarrierBlock

end YMGap.Continuum.XiExceptionalFinalCarrierFiberBlock
