/-
# Admissible occurrence sources and their exact component switch

The exceptional and nonexceptional branches share the same admissible source
domain.  This file extracts its predicate and same-side compatibility data
without assuming exceptionalness.  It then proves that the finite
source-dependent component switch is injective on that whole domain and
preserves the complete pair activity exactly.
-/

import YMGap.Continuum.XiExceptionalSourcePartition
import YMGap.Continuum.XiExceptionalSwitchedCompatibility
import YMGap.Continuum.XiExceptionalPathMaskAlgebra

namespace YMGap.Continuum.XiAdmissibleSourceSwitch

open YMGap.Constructive
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.AbstractPolymerXi
open YMGap.Continuum.XiPairSwitching
open YMGap.Continuum.XiReverseComponentRecovery
open YMGap.Continuum.XiExceptionalMaskCarrier
open YMGap.Continuum.XiExceptionalRecoveredBackground
open YMGap.Continuum.XiExceptionalDistinctInjection
open YMGap.Continuum.XiExceptionalOccurrenceCodes
open YMGap.Continuum.XiExceptionalSourceCodes
open YMGap.Continuum.XiExceptionalSourceWeight
open YMGap.Continuum.XiExceptionalPathMaskAlgebra
open YMGap.Continuum.XiExceptionalSwitchedCompatibility

variable {L : Lattice}
variable [DecidableEq L.Plaquette]

local infix:50 " ≈ " => Q'.eqv

structure AdmissibleSourceFacts
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) : Type where
  source_admissible : sourceAdmissible Gamma qP b1 b2 pair = true
  left_q : ∀ i, i < Gamma.length → pair.1.at i = true →
    qP (polyAt Gamma i) = true
  left_avoid : ∀ i, i < Gamma.length → pair.1.at i = true →
    b1 (polyAt Gamma i) = false
  right_q : ∀ i, i < Gamma.length → pair.2.at i = true →
    qP (polyAt Gamma i) = true
  right_avoid : ∀ i, i < Gamma.length → pair.2.at i = true →
    b2 (polyAt Gamma i) = false
  left_pairwise : ∀ i j, i ≠ j → pair.1.at i = true →
    pair.1.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true
  right_pairwise : ∀ i j, i ≠ j → pair.2.at i = true →
    pair.2.at j = true → compatibleB (polyAt Gamma i) (polyAt Gamma j) = true
  right_good : ∀ i, pair.2.at i = true → predAt Gamma b2 i = false
  left_family_compatible : familyCompatibleB (leftFamily Gamma pair) = true
  right_family_compatible : familyCompatibleB (rightFamily Gamma pair) = true

private theorem bitVec_true_lt {n : Nat} (bits : OccBitVec n)
    (i : Nat) (hi : bits.at i = true) : i < n := by
  cases hlt : decide (i < n) with
  | true => exact of_decide_eq_true hlt
  | false =>
      have hnlt : ¬ i < n := of_decide_eq_false hlt
      have hout := bitVec_at_false_of_ge bits i (by omega)
      rw [hi] at hout
      exact absurd hout (by decide)

private theorem selected_pairwise_of_compatible
    (Gamma : List (Polymer L)) (bits : OccBitVec Gamma.length)
    (hcompat : familyCompatibleB (selectByBits Gamma bits) = true) :
    ∀ i j, i ≠ j → bits.at i = true → bits.at j = true →
      compatibleB (polyAt Gamma i) (polyAt Gamma j) = true := by
  intro i j hij hi hj
  exact selectByBits_pairwise_compatible Gamma bits i j
    (bitVec_true_lt bits i hi) (bitVec_true_lt bits j hj) hij hi hj hcompat

def admissibleSourceFactsOfTrue
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hadmiss : sourceAdmissible Gamma qP b1 b2 pair = true) :
    AdmissibleSourceFacts Gamma qP b1 b2 pair := by
  unfold sourceAdmissible at hadmiss
  have hsides := (Bool.and_eq_true _ _).mp hadmiss
  have hleft := (Bool.and_eq_true _ _).mp hsides.1
  have hleftPred := (Bool.and_eq_true _ _).mp hleft.1
  have hright := (Bool.and_eq_true _ _).mp hsides.2
  have hrightPred := (Bool.and_eq_true _ _).mp hright.1
  have hleftQ := all_selectByBits_pointwise Gamma pair.1 qP hleftPred.1
  have hleftAvoidNot := all_selectByBits_pointwise Gamma pair.1
    (fun X => !(b1 X)) hleftPred.2
  have hrightQ := all_selectByBits_pointwise Gamma pair.2 qP hrightPred.1
  have hrightAvoidNot := all_selectByBits_pointwise Gamma pair.2
    (fun X => !(b2 X)) hrightPred.2
  have hleftAvoid : ∀ i, i < Gamma.length → pair.1.at i = true →
      b1 (polyAt Gamma i) = false := by
    intro i hi hbit
    exact eq_false_of_not_true (hleftAvoidNot i hi hbit)
  have hrightAvoid : ∀ i, i < Gamma.length → pair.2.at i = true →
      b2 (polyAt Gamma i) = false := by
    intro i hi hbit
    exact eq_false_of_not_true (hrightAvoidNot i hi hbit)
  have hrightGood : ∀ i, pair.2.at i = true → predAt Gamma b2 i = false := by
    intro i hbit
    have hi := bitVec_true_lt pair.2 i hbit
    simp [predAt, hrightAvoid i hi hbit]
  exact
    { source_admissible := hadmiss
      left_q := hleftQ
      left_avoid := hleftAvoid
      right_q := hrightQ
      right_avoid := hrightAvoid
      left_pairwise := selected_pairwise_of_compatible Gamma pair.1 hleft.2
      right_pairwise := selected_pairwise_of_compatible Gamma pair.2 hright.2
      right_good := hrightGood
      left_family_compatible := hleft.2
      right_family_compatible := hright.2 }

def admissibleSourceFactsOfMem
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length)
    (hmem : pair ∈
      XiExceptionalSourcePartition.admissibleSourceCodes Gamma qP b1 b2) :
    AdmissibleSourceFacts Gamma qP b1 b2 pair :=
  admissibleSourceFactsOfTrue Gamma qP b1 b2 pair
    (List.mem_filter.mp hmem).2

theorem switchedCode_at_left
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).1.at i =
      switchedLeft Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem switchedCode_at_right
    (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (pair : MaskPair Gamma.length) (i : Nat) (hi : i < Gamma.length) :
    (switchedBranchCode Gamma b2 pair).2.at i =
      switchedRight Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2) i := by
  unfold switchedBranchCode
  simpa using bitsFromMask_at Gamma.length _ 0 i hi

theorem switchedBranchCode_injective_of_admissible
    (Gamma : List (Polymer L)) (qP b1 b2 : Polymer L → Bool)
    (pair1 pair2 : MaskPair Gamma.length)
    (hadmiss1 : sourceAdmissible Gamma qP b1 b2 pair1 = true)
    (hadmiss2 : sourceAdmissible Gamma qP b1 b2 pair2 = true)
    (hcode : switchedBranchCode Gamma b2 pair1 =
      switchedBranchCode Gamma b2 pair2) :
    pair1 = pair2 := by
  let facts1 := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair1 hadmiss1
  let facts2 := admissibleSourceFactsOfTrue Gamma qP b1 b2 pair2 hadmiss2
  have hleftCode := congrArg Prod.fst hcode
  have hrightCode := congrArg Prod.snd hcode
  have houtLeft : ∀ i,
      switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2) i =
        switchedLeft Gamma.length (incAtDistinct Gamma)
          (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2) i := by
    intro i
    cases hi : decide (i < Gamma.length) with
    | true =>
        have hiN := of_decide_eq_true hi
        have hat := congrArg (fun bits => bits.at i) hleftCode
        change (switchedBranchCode Gamma b2 pair1).1.at i =
          (switchedBranchCode Gamma b2 pair2).1.at i at hat
        rw [switchedCode_at_left Gamma b2 pair1 i hiN,
          switchedCode_at_left Gamma b2 pair2 i hiN] at hat
        exact hat
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
        rw [switchedLeft_false_of_ge Gamma b2 pair1 i (by omega),
          switchedLeft_false_of_ge Gamma b2 pair2 i (by omega)]
  have houtRight : ∀ i,
      switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask pair1.1) (bitMask pair1.2) (predAt Gamma b2) i =
        switchedRight Gamma.length (incAtDistinct Gamma)
          (bitMask pair2.1) (bitMask pair2.2) (predAt Gamma b2) i := by
    intro i
    cases hi : decide (i < Gamma.length) with
    | true =>
        have hiN := of_decide_eq_true hi
        have hat := congrArg (fun bits => bits.at i) hrightCode
        change (switchedBranchCode Gamma b2 pair1).2.at i =
          (switchedBranchCode Gamma b2 pair2).2.at i at hat
        rw [switchedCode_at_right Gamma b2 pair1 i hiN,
          switchedCode_at_right Gamma b2 pair2 i hiN] at hat
        exact hat
    | false =>
        have hnlt : ¬ i < Gamma.length := of_decide_eq_false hi
        rw [switchedRight_false_of_ge Gamma b2 pair1 i (by omega),
          switchedRight_false_of_ge Gamma b2 pair2 i (by omega)]
  have hinj := distinct_switched_pair_injective Gamma b2
    (bitMask pair1.1) (bitMask pair1.2)
    (bitMask pair2.1) (bitMask pair2.2)
    facts1.left_pairwise facts1.right_pairwise facts1.right_good
    facts2.left_pairwise facts2.right_pairwise facts2.right_good
    houtLeft houtRight
  exact MaskPair.ext hinj.1 hinj.2

theorem switchedBranchCode_familyActivity_preserved
    (w : Q') (Gamma : List (Polymer L)) (b2 : Polymer L → Bool)
    (label : L.Plaquette → Rep) (pair : MaskPair Gamma.length) :
    familyActivity w
        (leftFamily Gamma (switchedBranchCode Gamma b2 pair)) label *
      familyActivity w
        (rightFamily Gamma (switchedBranchCode Gamma b2 pair)) label ≈
    familyActivity w (leftFamily Gamma pair) label *
      familyActivity w (rightFamily Gamma pair) label := by
  let switched := switchedBranchCode Gamma b2 pair
  have hleftOut :
      maskWeight w Gamma label (bitMask switched.1) =
        maskWeight w Gamma label
          (switchedLeft Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_left Gamma b2 pair i hi
  have hrightOut :
      maskWeight w Gamma label (bitMask switched.2) =
        maskWeight w Gamma label
          (switchedRight Gamma.length (incAtDistinct Gamma)
            (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2)) := by
    apply maskWeight_congr_on
    intro i hi
    exact switchedCode_at_right Gamma b2 pair i hi
  have hswitch :
      maskWeight w Gamma label (bitMask switched.1) *
          maskWeight w Gamma label (bitMask switched.2) ≈
        maskWeight w Gamma label (bitMask pair.1) *
          maskWeight w Gamma label (bitMask pair.2) := by
    rw [hleftOut, hrightOut]
    exact maskWeight_swap_preserved w Gamma label
      (forwardComponent Gamma.length (incAtDistinct Gamma)
        (bitMask pair.1) (bitMask pair.2) (predAt Gamma b2))
      (bitMask pair.1) (bitMask pair.2)
  have hsl := maskWeight_eqv_familyActivity w Gamma label (bitMask switched.1)
  have hsr := maskWeight_eqv_familyActivity w Gamma label (bitMask switched.2)
  have hl := maskWeight_eqv_familyActivity w Gamma label (bitMask pair.1)
  have hr := maskWeight_eqv_familyActivity w Gamma label (bitMask pair.2)
  rw [maskFamily_toMask_eq_selectByBits] at hsl hsr hl hr
  exact Q'.eqv_trans _ _ _
    (mul_eqv_congr_both (Q'.eqv_symm hsl) (Q'.eqv_symm hsr))
    (Q'.eqv_trans _ _ _ hswitch (mul_eqv_congr_both hl hr))

#print axioms admissibleSourceFactsOfTrue
#print axioms admissibleSourceFactsOfMem
#print axioms switchedCode_at_left
#print axioms switchedCode_at_right
#print axioms switchedBranchCode_injective_of_admissible
#print axioms switchedBranchCode_familyActivity_preserved

end YMGap.Continuum.XiAdmissibleSourceSwitch
