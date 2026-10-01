/-
# Complex separated Wilson words on the ORIGINAL physical bond completion

Each letter is the already constructed one-step-buffered physical insertion.
The componentwise extension acts on the existing complex bond completion,
preserves both constructive scalar moduli, and has word reversal as its full
Hermitian adjoint.  Its matrix elements remain the four original reflected
source limits.  No equal-time multiplication, locality, cyclicity, OS-root
inhabitant, physical-time group, or continuum statement is asserted.
-/

import YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSDerivative
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSeparatedWords

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (IntrinsicExpression unit)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (completedInner)
open YMGap.Continuum.BF4WilsonAllNomeBondOSCompletion
  (BondCompletion bondCompletedInner ofSource)
open YMGap.Continuum.BF4WilsonAllNomeBondOSTime
  (bondValue bondValue_injective bondValue_inner vacuum)
open YMGap.Continuum.BF4WilsonAllNomeBondOSLinear
  (bondValue_sub bondValue_zero)
open YMGap.Continuum.BF4WilsonAllNomeBondOSInsertion
  (act act_value act_add act_realSmul act_norm_bound act_root_pin)
open YMGap.Continuum.BF4WilsonAllNomeBondOSSeparatedWords
  (Word sourceWord wordAct wordAct_append wordAct_adjoint wordAct_ofSource vacuum_word)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion inner sourceForm source_pairing)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSTime
  (add smul)
open YMGap.Continuum.BF4WilsonAllNomeSectorInsertion (sandwich)
open YMGap.Continuum.BF4WilsonAllNomePositiveTimeLaws (positiveAction_sub)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedMultiply completedMultiply_add completedMultiply_smul completedMultiply_zero)
open YMGap.Continuum.BF4WilsonAllNomeNestedRootCompatibility (root_zero)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completedSub completedNeg)
open YMGap.Continuum.BF4WilsonAllNomeBilinearTime
  (completedInner_zero_left completedInner_zero_right)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "RH" => BondCompletion hw0 hw1 (width := width)
local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "B" => bondCompletedInner hw0 hw1
local notation "I" => inner hw0 hw1
local notation "Act" =>
  BF4WilsonAllNomeBondOSSeparatedWords.wordAct hw0 hw1
local notation "Z" => BF4WilsonAllNomeBondOSLinear.zero hw0 hw1 (width := width)

/-- Same represented source operation in each original real component. -/
def sourceWordPair (word : Word width)
    (x : BF4WilsonAllNomeComplexBondOSCompletion.Source width) :
    BF4WilsonAllNomeComplexBondOSCompletion.Source width :=
  (sourceWord word x.1,sourceWord word x.2)

/-- The bounded complex word operator on the EXISTING physical carrier. -/
def wordAct (word : Word width) (x : H) : H :=
  (Act word x.1,Act word x.2)

theorem wordAct_append (left right : Word width) (x : H) :
    wordAct hw0 hw1 (left ++ right) x =
      wordAct hw0 hw1 left (wordAct hw0 hw1 right x) := by
  apply Prod.ext
  · exact BF4WilsonAllNomeBondOSSeparatedWords.wordAct_append hw0 hw1 left right x.1
  · exact BF4WilsonAllNomeBondOSSeparatedWords.wordAct_append hw0 hw1 left right x.2

/-- Reversal is the FULL Hermitian adjoint, including the two imaginary cross
pairings, on every completed physical complex input. -/
theorem wordAct_adjoint (word : Word width) (x y : H) :
    I (wordAct hw0 hw1 word x) y =
      I x (wordAct hw0 hw1 word.reverse y) := by
  apply Prod.ext
  · change RCadd (B (Act word x.1) y.1) (B (Act word x.2) y.2) =
      RCadd (B x.1 (Act word.reverse y.1)) (B x.2 (Act word.reverse y.2))
    rw [BF4WilsonAllNomeBondOSSeparatedWords.wordAct_adjoint,
      BF4WilsonAllNomeBondOSSeparatedWords.wordAct_adjoint]
  · change RCsub (B (Act word x.1) y.2) (B (Act word x.2) y.1) =
      RCsub (B x.1 (Act word.reverse y.2)) (B x.2 (Act word.reverse y.1))
    rw [BF4WilsonAllNomeBondOSSeparatedWords.wordAct_adjoint,
      BF4WilsonAllNomeBondOSSeparatedWords.wordAct_adjoint]

private theorem realWord_add (word : Word width) (x y : RH) :
    Act word (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.add hw0 hw1 (Act word x) (Act word y) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2 (Act rest (BF4WilsonAllNomeBondOSLinear.add hw0 hw1 x y)) = _
      rw [ih,act_add]
      rfl

private theorem realWord_realSmul (word : Word width)
    (s : CReal) (cs : QCauchy s.approx) (x : RH) :
    Act word (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x) =
      BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs (Act word x) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2
        (Act rest (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x)) = _
      rw [ih,act_realSmul]
      rfl

private theorem multiplier_sub (L : SourceLoop width) (spin : Nat)
    (x y : BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width) :
    completedMultiply hw0 hw1 L spin (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1 (completedMultiply hw0 hw1 L spin x)
        (completedMultiply hw0 hw1 L spin y) := by
  simp only [completedSub,completedNeg,completedMultiply_add,completedMultiply_smul]

private theorem sandwich_sub (L : SourceLoop width) (spin : Nat)
    (x y : BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width) :
    sandwich hw0 hw1 (BF4WilsonAllNomeBondOSInsertion.halfTime) L spin
      (completedSub hw0 hw1 x y) =
      completedSub hw0 hw1
        (sandwich hw0 hw1 (BF4WilsonAllNomeBondOSInsertion.halfTime) L spin x)
        (sandwich hw0 hw1 (BF4WilsonAllNomeBondOSInsertion.halfTime) L spin y) := by
  simp only [sandwich,positiveAction_sub,multiplier_sub]

private theorem realAct_sub (L : SourceLoop width) (spin : Nat) (x y : RH) :
    act hw0 hw1 L spin (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
        (act hw0 hw1 L spin x) (act hw0 hw1 L spin y) := by
  apply bondValue_injective hw0 hw1
  rw [act_value,bondValue_sub,bondValue_sub,act_value,act_value]
  exact sandwich_sub hw0 hw1 L spin _ _

private theorem realWord_sub (word : Word width) (x y : RH) :
    Act word (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x y) =
      BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 (Act word x) (Act word y) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2
        (Act rest (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1 x y)) = _
      rw [ih,realAct_sub]
      rfl

theorem wordAct_add (word : Word width) (x y : H) :
    wordAct hw0 hw1 word (add hw0 hw1 x y) =
      add hw0 hw1 (wordAct hw0 hw1 word x) (wordAct hw0 hw1 word y) := by
  apply Prod.ext
  · exact realWord_add hw0 hw1 word x.1 y.1
  · exact realWord_add hw0 hw1 word x.2 y.2

/-- Complex linearity keeps both supplied constructive-real scalar moduli. -/
theorem wordAct_smul (word : Word width) (s t : CReal)
    (cs : QCauchy s.approx) (ct : QCauchy t.approx) (x : H) :
    wordAct hw0 hw1 word (smul hw0 hw1 s t cs ct x) =
      smul hw0 hw1 s t cs ct (wordAct hw0 hw1 word x) := by
  apply Prod.ext
  · change Act word (BF4WilsonAllNomeBondOSLinear.sub hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x.1)
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 t ct x.2)) = _
    rw [realWord_sub,realWord_realSmul,realWord_realSmul]
    rfl
  · change Act word (BF4WilsonAllNomeBondOSLinear.add hw0 hw1
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 t ct x.1)
      (BF4WilsonAllNomeBondOSLinear.realSmul hw0 hw1 s cs x.2)) = _
    rw [realWord_add,realWord_realSmul,realWord_realSmul]
    rfl

/-- An arbitrary PAIR of original finite sources remains an original pair. -/
theorem wordAct_ofSource (word : Word width)
    (x : BF4WilsonAllNomeComplexBondOSCompletion.Source width) :
    wordAct hw0 hw1 word
        (BF4WilsonAllNomeComplexBondOSCompletion.ofSource hw0 hw1 x) =
      BF4WilsonAllNomeComplexBondOSCompletion.ofSource hw0 hw1
        (sourceWordPair word x) := by
  apply Prod.ext
  · exact BF4WilsonAllNomeBondOSSeparatedWords.wordAct_ofSource hw0 hw1 word x.1
  · exact BF4WilsonAllNomeBondOSSeparatedWords.wordAct_ofSource hw0 hw1 word x.2

/-- All four mixed components are the unchanged ORIGINAL normalized reflected
source limits, not independently supplied matrix elements. -/
theorem wordAct_source_pairing (word : Word width)
    (x y : BF4WilsonAllNomeComplexBondOSCompletion.Source width) :
    I (BF4WilsonAllNomeComplexBondOSCompletion.ofSource hw0 hw1 x)
      (wordAct hw0 hw1 word
        (BF4WilsonAllNomeComplexBondOSCompletion.ofSource hw0 hw1 y)) =
      sourceForm hw0 hw1 x (sourceWordPair word y) := by
  rw [wordAct_ofSource,source_pairing]

/-- The original spin-only norm ceiling also holds on the physical complex
carrier for each buffered letter. -/
theorem letter_norm_bound (L : SourceLoop width) (spin : Nat) (x : H) :
    RCle (I (wordAct hw0 hw1 [(L,spin)] x)
      (wordAct hw0 hw1 [(L,spin)] x)).1
      (RCscale (YMGap.Continuum.QuaternionHaarPolynomialSquareBound.characterBound spin)
        (I x x).1) := by
  have h₁ := act_norm_bound hw0 hw1 L spin x.1
  have h₂ := act_norm_bound hw0 hw1 L spin x.2
  change RCle (RCadd (B (act hw0 hw1 L spin x.1) (act hw0 hw1 L spin x.1))
    (B (act hw0 hw1 L spin x.2) (act hw0 hw1 L spin x.2)))
    (RCscale _ (RCadd (B x.1 x.1) (B x.2 x.2)))
  rw [RCscale_RCadd]
  exact RCadd_le_add h₁ h₂

private theorem realAct_zero (L : SourceLoop width) (spin : Nat) :
    act hw0 hw1 L spin Z = Z := by
  apply bondValue_injective hw0 hw1
  rw [act_root_pin,bondValue_zero,root_zero,completedMultiply_zero,root_zero]

private theorem realWord_zero (word : Word width) : Act word Z = Z := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
      change act hw0 hw1 a.1 a.2 (Act rest Z) = Z
      rw [ih,realAct_zero]

private theorem b_zero_left (x : RH) : B Z x = RCzero := by
  rw [bondValue_inner,bondValue_zero,completedInner_zero_left]

private theorem b_zero_right (x : RH) : B x Z = RCzero := by
  rw [bondValue_inner,bondValue_zero,completedInner_zero_right]

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (CReal.sub_self_eqv_zero A)

/-- Complex vacuum words still evaluate the ORIGINAL normalized Wilson joint
limit, with zero imaginary part.  The vacuum is the existing physical pair. -/
theorem vacuum_word (word : Word width) :
    I (BF4WilsonAllNomeComplexBondOSDerivative.vacuum hw0 hw1)
      (wordAct hw0 hw1 word
        (BF4WilsonAllNomeComplexBondOSDerivative.vacuum hw0 hw1)) =
      (Quotient.mk crealSetoid (originalJointLimit hw0 hw1 (sourceWord word (unit width)).radius
        (sourceWord word (unit width)).expression
        (sourceWord word (unit width)).within), RCzero) := by
  change
    (RCadd (B (vacuum hw0 hw1) (Act word (vacuum hw0 hw1)))
      (B Z (Act word Z)),
     RCsub (B (vacuum hw0 hw1) (Act word Z))
       (B Z (Act word (vacuum hw0 hw1)))) = _
  rw [realWord_zero, b_zero_left, b_zero_right, b_zero_left,
    rc_add_zero,rc_sub_self,
    BF4WilsonAllNomeBondOSSeparatedWords.vacuum_word]
  rfl

#print axioms sourceWordPair
#print axioms wordAct
#print axioms wordAct_append
#print axioms wordAct_adjoint
#print axioms wordAct_add
#print axioms wordAct_smul
#print axioms wordAct_ofSource
#print axioms wordAct_source_pairing
#print axioms letter_norm_bound
#print axioms vacuum_word

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSSeparatedWords
