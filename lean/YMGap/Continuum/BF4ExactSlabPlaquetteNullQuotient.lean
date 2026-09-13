/-
# Null quotient of the ORIGINAL normalized plaquette reflected form

Two actual plaquette expressions have zero reflected squared distance iff
they pair equally with every expression. This constructs the null setoid,
descends the SAME original normalized form, and proves positive definiteness
on that quotient. The distinguished unit has norm one and is not zero.

This is a finite-slab plaquette-subalgebra quotient, not yet its Hilbert
completion, all gauge observables, a stationary vacuum or a time operator.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
import YMGap.Continuum.RCBilinearDifference

namespace YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm

def zeroExpression (half : Nat) : PlaquetteExpression half := .smul 0 .unit

def subtract {half : Nat} (e f : PlaquetteExpression half) : PlaquetteExpression half :=
  .add e (.smul (-1) f)

private theorem rc_sub_self (a : RC) : RCsub a a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

private theorem rc_zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem rc_sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (QPoly.q_add_zero_eqv (A.approx n))))

private theorem rc_eq_of_sub_zero {a b : RC} (h : RCsub a b = RCzero) : a = b := by
  have hc : RCadd (RCsub a b) b = a := by
    refine Quotient.inductionOn₂ a b ?_
    intro A B
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.sub_add_cancel_eqv (A.approx n) (B.approx n)))
  rw [h, rc_zero_add] at hc
  exact hc.symm

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

def pairing (e f : PlaquetteExpression half) : RC := Quotient.mk crealSetoid (form w hw0 hw1 e f)

theorem pairing_symm (e f : PlaquetteExpression half) :
    pairing w hw0 hw1 e f = pairing w hw0 hw1 f e :=
  Quotient.sound (form_symm w hw0 hw1 e f)

theorem pairing_congr {e e' f f' : PlaquetteExpression half}
    (he : expressionEqv e e') (hf : expressionEqv f f') :
    pairing w hw0 hw1 e f = pairing w hw0 hw1 e' f' :=
  Quotient.sound (form_congr w hw0 hw1 he hf)

theorem pairing_add_left (e f g : PlaquetteExpression half) :
    pairing w hw0 hw1 (.add e f) g = RCadd (pairing w hw0 hw1 e g) (pairing w hw0 hw1 f g) :=
  Quotient.sound (form_add_left w hw0 hw1 e f g)

theorem pairing_add_right (e f g : PlaquetteExpression half) :
    pairing w hw0 hw1 e (.add f g) = RCadd (pairing w hw0 hw1 e f) (pairing w hw0 hw1 e g) :=
  Quotient.sound (form_add_right w hw0 hw1 e f g)

theorem pairing_smul_left (c : Q') (e f : PlaquetteExpression half) :
    pairing w hw0 hw1 (.smul c e) f = RCmul (Quotient.mk crealSetoid (ofQ' c)) (pairing w hw0 hw1 e f) :=
  Quotient.sound (form_smul_left w hw0 hw1 c e f)

theorem pairing_neg_left (e f : PlaquetteExpression half) :
    pairing w hw0 hw1 (.smul (-1) e) f = RCneg (pairing w hw0 hw1 e f) :=
  Quotient.sound ((form_smul_left w hw0 hw1 (-1) e f).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n =>
      Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 ((form w hw0 hw1 e f).approx n))
        (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv _)))))

theorem pairing_sub_left (e f g : PlaquetteExpression half) :
    pairing w hw0 hw1 (subtract e f) g = RCsub (pairing w hw0 hw1 e g) (pairing w hw0 hw1 f g) := by
  change pairing w hw0 hw1 (.add e (.smul (-1) f)) g = _
  rw [pairing_add_left, pairing_neg_left]
  rfl

theorem pairing_sub_right (e f g : PlaquetteExpression half) :
    pairing w hw0 hw1 e (subtract f g) = RCsub (pairing w hw0 hw1 e f) (pairing w hw0 hw1 e g) := by
  rw [pairing_symm w hw0 hw1 e (subtract f g), pairing_sub_left,
    pairing_symm w hw0 hw1 f e, pairing_symm w hw0 hw1 g e]

theorem pairing_zero_left (e : PlaquetteExpression half) :
    pairing w hw0 hw1 (zeroExpression half) e = RCzero :=
  Quotient.sound ((form_smul_left w hw0 hw1 0 .unit e).trans
    (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv ((form w hw0 hw1 .unit e).approx n))))

theorem pairing_zero_right (e : PlaquetteExpression half) :
    pairing w hw0 hw1 e (zeroExpression half) = RCzero :=
  (pairing_symm w hw0 hw1 e _).trans (pairing_zero_left w hw0 hw1 e)

theorem pairing_nonnegative (e : PlaquetteExpression half) : RCnonneg (pairing w hw0 hw1 e e) :=
  form_nonnegative w hw0 hw1 e

theorem pairing_radical_zero (e f : PlaquetteExpression half)
    (he : pairing w hw0 hw1 e e = RCzero) : pairing w hw0 hw1 e f = RCzero :=
  Quotient.sound (form_radical_zero w hw0 hw1 e f (Quotient.exact he))

def Null (e f : PlaquetteExpression half) : Prop :=
  pairing w hw0 hw1 (subtract e f) (subtract e f) = RCzero

/-- The norm radical is exactly equality of all mixed pairings. -/
theorem null_iff_pairing (e f : PlaquetteExpression half) :
    Null w hw0 hw1 e f ↔ ∀ g, pairing w hw0 hw1 e g = pairing w hw0 hw1 f g := by
  constructor
  · intro h g
    have hz := pairing_radical_zero w hw0 hw1 (subtract e f) g h
    rw [pairing_sub_left] at hz
    exact rc_eq_of_sub_zero hz
  · intro h
    unfold Null
    rw [pairing_sub_left, h (subtract e f), rc_sub_self]

def nullSetoid (half : Nat) : Setoid (PlaquetteExpression half) where
  r := Null w hw0 hw1
  iseqv := ⟨fun e => (null_iff_pairing w hw0 hw1 e e).mpr (fun _ => rfl),
    fun h => (null_iff_pairing w hw0 hw1 _ _).mpr (fun g => ((null_iff_pairing w hw0 hw1 _ _).mp h g).symm),
    fun h h' => (null_iff_pairing w hw0 hw1 _ _).mpr (fun g =>
      ((null_iff_pairing w hw0 hw1 _ _).mp h g).trans ((null_iff_pairing w hw0 hw1 _ _).mp h' g))⟩

theorem pairing_null_congr {e e' f f' : PlaquetteExpression half}
    (he : Null w hw0 hw1 e e') (hf : Null w hw0 hw1 f f') :
    pairing w hw0 hw1 e f = pairing w hw0 hw1 e' f' := by
  rw [(null_iff_pairing w hw0 hw1 _ _).mp he f, pairing_symm w hw0 hw1 e' f,
    (null_iff_pairing w hw0 hw1 _ _).mp hf e', pairing_symm w hw0 hw1 f' e']

theorem null_zero_iff (e : PlaquetteExpression half) :
    Null w hw0 hw1 e (zeroExpression half) ↔ pairing w hw0 hw1 e e = RCzero := by
  unfold Null
  rw [pairing_sub_left, pairing_zero_left, rc_sub_zero,
    pairing_sub_right, pairing_zero_right, rc_sub_zero]

theorem null_add {e e' f f' : PlaquetteExpression half}
    (he : Null w hw0 hw1 e e') (hf : Null w hw0 hw1 f f') :
    Null w hw0 hw1 (.add e f) (.add e' f') := by
  apply (null_iff_pairing w hw0 hw1 _ _).mpr
  intro g
  rw [pairing_add_left, pairing_add_left, (null_iff_pairing w hw0 hw1 _ _).mp he g,
    (null_iff_pairing w hw0 hw1 _ _).mp hf g]

theorem null_smul (c : Q') {e f : PlaquetteExpression half} (h : Null w hw0 hw1 e f) :
    Null w hw0 hw1 (.smul c e) (.smul c f) := by
  apply (null_iff_pairing w hw0 hw1 _ _).mpr
  intro g
  rw [pairing_smul_left, pairing_smul_left, (null_iff_pairing w hw0 hw1 _ _).mp h g]

def Carrier (half : Nat) : Type := Quotient (nullSetoid w hw0 hw1 half)

def embed (e : PlaquetteExpression half) : Carrier w hw0 hw1 half := Quotient.mk _ e

def inner : Carrier w hw0 hw1 half → Carrier w hw0 hw1 half → RC :=
  Quotient.lift₂ (pairing w hw0 hw1) (fun _ _ _ _ he hf => pairing_null_congr w hw0 hw1 he hf)

def zero (half : Nat) : Carrier w hw0 hw1 half := embed w hw0 hw1 (zeroExpression half)

def unit (half : Nat) : Carrier w hw0 hw1 half := embed w hw0 hw1 .unit

def add : Carrier w hw0 hw1 half → Carrier w hw0 hw1 half → Carrier w hw0 hw1 half :=
  Quotient.lift₂ (fun e f => embed w hw0 hw1 (.add e f))
    (fun _ _ _ _ he hf => Quotient.sound (null_add w hw0 hw1 he hf))

def smul (c : Q') : Carrier w hw0 hw1 half → Carrier w hw0 hw1 half :=
  Quotient.lift (fun e => embed w hw0 hw1 (.smul c e))
    (fun _ _ h => Quotient.sound (null_smul w hw0 hw1 c h))

theorem inner_embed (e f : PlaquetteExpression half) :
    inner w hw0 hw1 (embed w hw0 hw1 e) (embed w hw0 hw1 f) = pairing w hw0 hw1 e f := rfl

theorem inner_symm (x y : Carrier w hw0 hw1 half) : inner w hw0 hw1 x y = inner w hw0 hw1 y x := by
  refine Quotient.inductionOn₂ x y ?_
  exact pairing_symm w hw0 hw1

theorem inner_nonnegative (x : Carrier w hw0 hw1 half) : RCnonneg (inner w hw0 hw1 x x) := by
  refine Quotient.inductionOn x ?_
  exact pairing_nonnegative w hw0 hw1

theorem inner_add_left (x y z : Carrier w hw0 hw1 half) :
    inner w hw0 hw1 (add w hw0 hw1 x y) z = RCadd (inner w hw0 hw1 x z) (inner w hw0 hw1 y z) := by
  refine Quotient.inductionOn₃ x y z ?_
  exact pairing_add_left w hw0 hw1

theorem inner_smul_left (c : Q') (x y : Carrier w hw0 hw1 half) :
    inner w hw0 hw1 (smul w hw0 hw1 c x) y = RCmul (Quotient.mk crealSetoid (ofQ' c)) (inner w hw0 hw1 x y) := by
  refine Quotient.inductionOn₂ x y ?_
  exact pairing_smul_left w hw0 hw1 c

theorem inner_cauchySchwarz (x y : Carrier w hw0 hw1 half) :
    RCle (RCmul (inner w hw0 hw1 x y) (inner w hw0 hw1 x y))
      (RCmul (inner w hw0 hw1 x x) (inner w hw0 hw1 y y)) := by
  refine Quotient.inductionOn₂ x y ?_
  exact form_cauchySchwarz w hw0 hw1

theorem inner_posdef (x : Carrier w hw0 hw1 half) :
    inner w hw0 hw1 x x = RCzero ↔ x = zero w hw0 hw1 half := by
  refine Quotient.inductionOn x ?_
  intro e
  exact ⟨fun h => Quotient.sound ((null_zero_iff w hw0 hw1 e).mpr h),
    fun h => (null_zero_iff w hw0 hw1 e).mp (Quotient.exact h)⟩

theorem unit_norm_one (half : Nat) :
    inner w hw0 hw1 (unit w hw0 hw1 half) (unit w hw0 hw1 half) = Quotient.mk crealSetoid cone :=
  Quotient.sound (form_unit w hw0 hw1 half)

theorem unit_ne_zero (half : Nat) : unit w hw0 hw1 half ≠ zero w hw0 hw1 half := by
  intro h
  have hz := (inner_posdef w hw0 hw1 (unit w hw0 hw1 half)).mpr h
  rw [unit_norm_one] at hz
  have hreal : Equiv cone czero := Quotient.exact hz
  obtain ⟨N, hN⟩ := hreal HalfPow.half (by decide)
  exact (by decide : ¬ ((1 : Q') ≤ 0 + HalfPow.half)) (hN N (Nat.le_refl N)).1

end YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_add_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_neg_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_sub_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_sub_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_zero_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_zero_right
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_radical_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.null_iff_pairing
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.nullSetoid
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.pairing_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.null_zero_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.null_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.null_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.Carrier
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.embed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.unit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_embed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_add_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_smul_left
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_cauchySchwarz
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.inner_posdef
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.unit_norm_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient.unit_ne_zero
