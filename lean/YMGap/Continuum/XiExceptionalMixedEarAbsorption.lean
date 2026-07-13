/-
# Ear absorption on the mixed residual six-cycle

This module is deliberately separate from the frozen mixed-component fence.
It constructs two repeated-edge carrier walks.  Each walk absorbs one of the
two residual ears into the chain, while the other will be used as the
complementary member of a two-code weight block.
-/

import YMGap.Continuum.XiExceptionalComponentSummation

namespace YMGap.Continuum.XiExceptionalMixedEarAbsorption

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalPathExtraction
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalPathEncoder
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalCarrierCode
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalWeightedInjection

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one]; ac_rfl))

abbrev TL := toyLattice
private instance instDecidableEqTLPlaquette : DecidableEq TL.Plaquette :=
  show DecidableEq (Nat × Nat) from inferInstance

def e0 : TL.Plaquette := (0, 0)
def e1 : TL.Plaquette := (1, 0)
def e2 : TL.Plaquette := (2, 0)
def e3 : TL.Plaquette := (3, 0)
def e4 : TL.Plaquette := (4, 0)
def e5 : TL.Plaquette := (5, 0)

def V0 : Polymer TL := [e5, e0]
def V1 : Polymer TL := [e0, e1]
def V2 : Polymer TL := [e1, e2]
def V3 : Polymer TL := [e2, e3]
def V4 : Polymer TL := [e3, e4]
def V5 : Polymer TL := [e4, e5]

def Gamma : List (Polymer TL) := [V0, V1, V2, V3, V4, V5]
def qAll : Polymer TL → Bool := fun _ => true
def markV0 : Polymer TL → Bool := fun X => decide (X = V0)
def badV3 : Polymer TL → Bool := fun X => decide (X = V3)

def bits6 (x0 x1 x2 x3 x4 x5 : Bool) : OccBitVec 6 :=
  .cons x0 (.cons x1 (.cons x2 (.cons x3 (.cons x4 (.cons x5 .nil)))))

def pair : MaskPair Gamma.length :=
  (bits6 false true false true false true,
    bits6 true false true false true false)

abbrev cycleEdge := disagreementEdge Gamma.length
  (incAtDistinct Gamma) (bitMask pair.1) (bitMask pair.2)

def emptyBits : OccBitVec Gamma.length :=
  bits6 false false false false false false

/-- Absorb the `1--2` ear by traversing it twice before reaching `3`. -/
def leftEarWalk : CWalk cycleEdge 0 3 :=
  .cons (x := 0) (y := 1) (by rfl)
    (.cons (x := 1) (y := 2) (by rfl)
      (.cons (x := 2) (y := 1) (by rfl)
        (.cons (x := 1) (y := 2) (by rfl)
          (.cons (x := 2) (y := 3) (by rfl) (.single 3)))))

/-- Absorb the `5--4` ear by traversing it twice before reaching `3`. -/
def rightEarWalk : CWalk cycleEdge 0 3 :=
  .cons (x := 0) (y := 5) (by rfl)
    (.cons (x := 5) (y := 4) (by rfl)
      (.cons (x := 4) (y := 5) (by rfl)
        (.cons (x := 5) (y := 4) (by rfl)
          (.cons (x := 4) (y := 3) (by rfl) (.single 3)))))

def leftEarCode : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk leftEarWalk emptyBits }
    external := emptyBits }

def rightEarCode : OccCarrierXiCodeAt Gamma :=
  { carrier :=
      { start := 0
        chain := occurrenceChainCodeOfWalk rightEarWalk emptyBits }
    external := emptyBits }

private theorem earCode_mem
    (walk : CWalk cycleEdge 0 3)
    (hlen : walk.vertices.length ≤ Gamma.length)
    (hbound : ∀ i, i ∈ walk.vertices → i < Gamma.length) :
    { carrier :=
        { start := 0
          chain := occurrenceChainCodeOfWalk walk emptyBits }
      external := emptyBits } ∈ occurrenceCarrierXiCodes Gamma := by
  unfold occurrenceCarrierXiCodes
  apply List.mem_flatMap.mpr
  refine ⟨emptyBits, bitVectors_complete emptyBits, ?_⟩
  apply List.mem_map.mpr
  refine ⟨⟨0, occurrenceChainCodeOfWalk walk emptyBits⟩, ?_, rfl⟩
  unfold occurrenceCarrierCodes
  apply List.mem_flatMap.mpr
  refine ⟨0, occurrenceIndices_complete (by simp [Gamma]), ?_⟩
  apply List.mem_map.mpr
  refine ⟨occurrenceChainCodeOfWalk walk emptyBits, ?_, rfl⟩
  exact occurrenceChainCodeOfWalk_mem Gamma emptyBits walk Gamma.length
    hlen hbound

theorem leftEarCode_mem :
    leftEarCode ∈ occurrenceCarrierXiCodes Gamma := by
  unfold leftEarCode
  apply earCode_mem leftEarWalk
  · exact Nat.le_refl _
  · intro i hi
    simp [leftEarWalk, CWalk.vertices, Gamma] at hi ⊢
    omega

theorem rightEarCode_mem :
    rightEarCode ∈ occurrenceCarrierXiCodes Gamma := by
  unfold rightEarCode
  apply earCode_mem rightEarWalk
  · exact Nat.le_refl _
  · intro i hi
    simp [rightEarWalk, CWalk.vertices, Gamma] at hi ⊢
    omega

theorem leftEarCode_erasure : eraseOccCarrierXiCode Gamma leftEarCode =
    ((V0, .step V1 (.step V2 (.step V1 (.step V2
      (.step V3 (.terminal [])))))), []) := by
  rfl

theorem rightEarCode_erasure : eraseOccCarrierXiCode Gamma rightEarCode =
    ((V0, .step V5 (.step V4 (.step V5 (.step V4
      (.step V3 (.terminal [])))))), []) := by
  rfl

private theorem mark_start : markV0 V0 = true := by rfl
private theorem bad_finish : badV3 V3 = true := by rfl
private theorem c01 : compatibleB V0 V1 = false := by rfl
private theorem c12 : compatibleB V1 V2 = false := by rfl
private theorem c21 : compatibleB V2 V1 = false := by rfl
private theorem c23 : compatibleB V2 V3 = false := by rfl
private theorem c05 : compatibleB V0 V5 = false := by rfl
private theorem c54 : compatibleB V5 V4 = false := by rfl
private theorem c45 : compatibleB V4 V5 = false := by rfl
private theorem c43 : compatibleB V4 V3 = false := by rfl

/-- The left ear code has the monomial obtained by repeating `V1,V2`. -/
theorem leftEarCode_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        leftEarCode ≈
      activity w V0 label *
        (activity w V1 label *
          (activity w V2 label *
            (activity w V1 label *
              (activity w V2 label * activity w V3 label)))) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
    leftEarCode = carrierXiCodeWeight w qAll markV0 badV3 Gamma label
      (eraseOccCarrierXiCode Gamma leftEarCode) from rfl]
  rw [leftEarCode_erasure]
  simp only [carrierXiCodeWeight, carrierCodeWeight, qAll, mark_start,
    Bool.true_and, if_true, chainCodeWeight, c01, c12, c21, c23,
    Bool.not_false, Bool.and_self, bad_finish, admissibleFamilyWeight,
    List.all_nil, familyCompatibleB_nil, familyActivity_nil]
  ring_qeqv

/-- The right ear code has the monomial obtained by repeating `V5,V4`. -/
theorem rightEarCode_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        rightEarCode ≈
      activity w V0 label *
        (activity w V5 label *
          (activity w V4 label *
            (activity w V5 label *
              (activity w V4 label * activity w V3 label)))) := by
  rw [show occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
    rightEarCode = carrierXiCodeWeight w qAll markV0 badV3 Gamma label
      (eraseOccCarrierXiCode Gamma rightEarCode) from rfl]
  rw [rightEarCode_erasure]
  simp only [carrierXiCodeWeight, carrierCodeWeight, qAll, mark_start,
    Bool.true_and, if_true, chainCodeWeight, c05, c54, c45, c43,
    Bool.not_false, Bool.and_self, bad_finish, admissibleFamilyWeight,
    List.all_nil, familyCompatibleB_nil, familyActivity_nil]
  ring_qeqv

/-! ## The two-code ear block -/

theorem pair_mem :
    pair ∈ exceptionalSourceCodes Gamma qAll markV0 badV3 := by
  apply List.mem_filter.mpr
  refine ⟨maskPairs_complete pair, ?_⟩
  rfl

private theorem left_family : leftFamily Gamma pair = [V1, V3, V5] := by
  rfl

private theorem right_family : rightFamily Gamma pair = [V0, V2, V4] := by
  rfl

def commonWeight (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V0 label * activity w V3 label

def leftArm (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V1 label * activity w V2 label

def rightArm (w : Q') (label : TL.Plaquette → Rep) : Q' :=
  activity w V5 label * activity w V4 label

/-- The checked mixed source is the product of its common endpoints and the
two complementary residual arms. -/
theorem mixedSource_weight_eqv (w : Q') (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≈
      commonWeight w label * (leftArm w label * rightArm w label) := by
  rw [occurrencePairWeight_eq_source_activity_of_mem
    w qAll markV0 badV3 Gamma label pair pair_mem]
  rw [left_family, right_family]
  simp only [familyActivity_cons, familyActivity_nil]
  unfold commonWeight leftArm rightArm
  ring_qeqv

/-- Constructive totality of the exact rational order. -/
private theorem q_le_total (a b : Q') : a ≤ b ∨ b ≤ a := by
  show a.num * (b.den : Int) ≤ b.num * (a.den : Int) ∨
    b.num * (a.den : Int) ≤ a.num * (b.den : Int)
  exact Int.le_total _ _

/-- The mixed product of two nonnegative arms is bounded by the sum of the
two repeated-arm products.  This is the algebraic ear-absorption budget. -/
theorem prod_le_square_sum {A B : Q'} (hA : (0 : Q') ≤ A)
    (hB : (0 : Q') ≤ B) : A * B ≤ A * A + B * B := by
  have hAA : (0 : Q') ≤ A * A := Q'.mul_nonneg A A hA hA
  have hBB : (0 : Q') ≤ B * B := Q'.mul_nonneg B B hB hB
  rcases q_le_total A B with hAB | hBA
  · have hmul : A * B ≤ B * B :=
      Q'.mul_le_mul_of_nonneg_right A B B hAB hB
    have hadd : B * B ≤ B * B + A * A :=
      Q'.add_le_self_of_nonneg (B * B) (A * A) hAA
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (Q'.add_comm_eqv (B * B) (A * A))))
  · have hmul : A * B ≤ A * A :=
      Q'.mul_le_mul_of_nonneg_left B A A hBA hA
    exact Q'.le_trans' _ _ _ hmul
      (Q'.add_le_self_of_nonneg (A * A) (B * B) hBB)

private theorem scaled_prod_le_square_sum {A B C : Q'}
    (hA : (0 : Q') ≤ A) (hB : (0 : Q') ≤ B)
    (hC : (0 : Q') ≤ C) :
    C * (A * B) ≤ C * (A * A + B * B) :=
  Q'.mul_le_mul_of_nonneg_left (A * B) (A * A + B * B) C
    (prod_le_square_sum hA hB) hC

theorem mixedEarCodes_ne : leftEarCode ≠ rightEarCode := by
  intro h
  have he := congrArg (eraseOccCarrierXiCode Gamma) h
  rw [leftEarCode_erasure, rightEarCode_erasure] at he
  cases he

def mixedEarBlock : List (OccCarrierXiCodeAt Gamma) :=
  [leftEarCode, rightEarCode]

theorem mixedEarBlock_nodup : mixedEarBlock.Nodup := by
  simp [mixedEarBlock, mixedEarCodes_ne]

theorem mixedEarBlock_mem (code : OccCarrierXiCodeAt Gamma)
    (hcode : code ∈ mixedEarBlock) :
    code ∈ occurrenceCarrierXiCodes Gamma := by
  unfold mixedEarBlock at hcode
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hcode
  rcases hcode with rfl | hcode
  · exact leftEarCode_mem
  · exact hcode ▸ rightEarCode_mem

theorem leftEarCode_square_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        leftEarCode ≈
      commonWeight w label * (leftArm w label * leftArm w label) := by
  refine Q'.eqv_trans _ _ _ (leftEarCode_weight_eqv w label) ?_
  unfold commonWeight leftArm
  ring_qeqv

theorem rightEarCode_square_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label
        rightEarCode ≈
      commonWeight w label * (rightArm w label * rightArm w label) := by
  refine Q'.eqv_trans _ _ _ (rightEarCode_weight_eqv w label) ?_
  unfold commonWeight rightArm
  ring_qeqv

theorem mixedEarBlock_weight_eqv
    (w : Q') (label : TL.Plaquette → Rep) :
    qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        mixedEarBlock ≈
      commonWeight w label *
        (leftArm w label * leftArm w label +
          rightArm w label * rightArm w label) := by
  simp only [mixedEarBlock, qListSum_cons, qListSum_nil, Q'.add_zero']
  refine Q'.eqv_trans _
    (commonWeight w label * (leftArm w label * leftArm w label) +
      commonWeight w label * (rightArm w label * rightArm w label)) _ ?_ ?_
  · exact add_eqv_congr_both _ _ _ _
      (leftEarCode_square_weight_eqv w label)
      (rightEarCode_square_weight_eqv w label)
  · ring_qeqv

/-- The mixed residual six-cycle source is absorbed by two genuine,
distinct carrier codes.  No arm-size comparison is assumed: rational
totality chooses the larger square constructively. -/
theorem mixedSource_le_mixedEarBlock {w : Q'} (hw : (0 : Q') ≤ w)
    (label : TL.Plaquette → Rep) :
    occurrencePairWeight w qAll markV0 badV3 Gamma label pair ≤
      qListSum
        (occurrenceCarrierXiCodeWeight w qAll markV0 badV3 Gamma label)
        mixedEarBlock := by
  have hA : (0 : Q') ≤ leftArm w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V1 label)
      (activity_nonneg hw V2 label)
  have hB : (0 : Q') ≤ rightArm w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V5 label)
      (activity_nonneg hw V4 label)
  have hC : (0 : Q') ≤ commonWeight w label :=
    Q'.mul_nonneg _ _ (activity_nonneg hw V0 label)
      (activity_nonneg hw V3 label)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (mixedSource_weight_eqv w label))
    (Q'.le_trans' _ _ _ (scaled_prod_le_square_sum hA hB hC)
      (Q'.ge_of_eqv (mixedEarBlock_weight_eqv w label)))

#print axioms leftEarCode_mem
#print axioms rightEarCode_mem
#print axioms leftEarCode_erasure
#print axioms rightEarCode_erasure
#print axioms leftEarCode_weight_eqv
#print axioms rightEarCode_weight_eqv
#print axioms pair_mem
#print axioms mixedSource_weight_eqv
#print axioms prod_le_square_sum
#print axioms mixedEarCodes_ne
#print axioms mixedEarBlock_nodup
#print axioms mixedEarBlock_mem
#print axioms leftEarCode_square_weight_eqv
#print axioms rightEarCode_square_weight_eqv
#print axioms mixedEarBlock_weight_eqv
#print axioms mixedSource_le_mixedEarBlock

end YMGap.Continuum.XiExceptionalMixedEarAbsorption
