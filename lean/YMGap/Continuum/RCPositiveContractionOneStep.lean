/-
# The one-step contraction identity for constructive-real forms

The algebraic identity P-P^3=(I-P)P(I-P)+2P(I-P)P works over the
constructive real quotient just as over rationals. It needs no spectral
theorem, square root, inverse, strict gap, or choice of representatives.
Quotient induction below proves scalar identities only; the vector carrier
and its same action remain arbitrary and unchanged.
-/

import YMGap.Continuum.PositiveContractionOneStepForm
import YMGap.Continuum.FCLimitContinuity
import YMGap.Continuum.BoundedTransferCalculus

namespace YMGap.Continuum.RCPositiveContractionOneStep

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal

local infixl:65 " +ᵣ " => RCadd
local prefix:75 "-ᵣ" => RCneg

private theorem zero_add (a : RC) : RCzero +ᵣ a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem neg_add (a b : RC) : -ᵣ(a +ᵣ b) = (-ᵣa) +ᵣ (-ᵣb) := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_add_eqv _ _))

private theorem neg_neg (a : RC) : -ᵣ(-ᵣa) = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.neg_neg_eqv (A.approx n)))

private theorem add_neg (a : RC) : a +ᵣ (-ᵣa) = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.add_neg_self_eqv (A.approx n)))

theorem scale_neg_one (a : RC) : RCscale (-1) a = -ᵣa := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv 1 (A.approx n))
      (Q'.neg_eqv_congr _ _ (Q'.one_mul_eqv (A.approx n)))))

private theorem neg_num (a : Q') : (-a).num = -a.num := rfl

private theorem balance (a b c : RC) :
    (((a +ᵣ (-ᵣb)) +ᵣ ((-ᵣb) +ᵣ c)) +ᵣ
      ((b +ᵣ (-ᵣc)) +ᵣ (b +ᵣ (-ᵣc)))) +ᵣ c = a := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv
    (((A.approx n + -(B.approx n)) + (-(B.approx n) + C.approx n)) +
      ((B.approx n + -(C.approx n)) + (B.approx n + -(C.approx n))) + C.approx n)
    (A.approx n)
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

/-- The three-moment inequality, using only ordered addition in RC. -/
theorem three_moment (a b c : RC)
    (hfirst : RCnonneg ((a +ᵣ (-ᵣb)) +ᵣ ((-ᵣb) +ᵣ c)))
    (hsecond : RCle c b) : RCle c a := by
  have hs := RCadd_le_add hsecond (RCle_refl (-ᵣc))
  rw [add_neg] at hs
  have hsum := RCadd_le_add hfirst (RCadd_le_add hs hs)
  simp only [zero_add] at hsum
  have hfinal := RCadd_le_add hsum (RCle_refl c)
  rw [zero_add, balance] at hfinal
  exact hfinal

private theorem sub_diagonal {V : Type} (addV : V → V → V) (negV : V → V) (E : V → V → RC)
    (hadd : ∀ x y z, E (addV x y) z = E x z +ᵣ E y z)
    (hneg : ∀ x y, E (negV x) y = -ᵣ(E x y))
    (hsym : ∀ x y, E x y = E y x) (a b : V) :
    E (addV a (negV b)) (addV a (negV b)) =
      (E a a +ᵣ (-ᵣ(E a b))) +ᵣ ((-ᵣ(E b a)) +ᵣ E b b) := by
  have hright : ∀ x y z, E x (addV y z) = E x y +ᵣ E x z := by
    intro x y z
    rw [hsym x (addV y z), hadd, hsym y x, hsym z x]
  have hnright : ∀ x y, E x (negV y) = -ᵣ(E x y) := by
    intro x y
    rw [hsym x (negV y), hneg, hsym y x]
  rw [hadd, hright, hnright, hneg, hright, hnright, neg_add, neg_neg]

/-- The SAME positive contraction contracts its one-step form over RC. -/
theorem oneStep_contraction {V : Type} (addV : V → V → V) (negV : V → V)
    (B : V → V → RC) (P : V → V)
    (hadd : ∀ x y z, B (addV x y) z = B x z +ᵣ B y z)
    (hneg : ∀ x y, B (negV x) y = -ᵣ(B x y))
    (hsym : ∀ x y, B x y = B y x)
    (hsa : ∀ x y, B x (P y) = B (P x) y)
    (hpos : ∀ x, RCnonneg (B x (P x)))
    (hupper : ∀ x, RCle (B x (P x)) (B x x)) (a : V) :
    RCle (B (P a) (P (P a))) (B a (P a)) := by
  let E := fun x y => B x (P y)
  have hEsym : ∀ x y, E x y = E y x := fun x y => Eq.trans (hsa x y) (hsym (P x) y)
  have he := sub_diagonal addV negV E (fun x y z => hadd x y (P z))
    (fun x y => hneg x (P y)) hEsym a (P a)
  have hp := hpos (addV a (negV (P a)))
  change RCnonneg (E (addV a (negV (P a))) (addV a (negV (P a)))) at hp
  rw [he] at hp
  change RCnonneg ((B a (P a) +ᵣ (-ᵣ(B a (P (P a))))) +ᵣ
    ((-ᵣ(B (P a) (P a))) +ᵣ B (P a) (P (P a)))) at hp
  rw [hsa a (P a)] at hp
  exact three_moment _ _ _ hp (hupper (P a))

end YMGap.Continuum.RCPositiveContractionOneStep

#print axioms YMGap.Continuum.RCPositiveContractionOneStep.scale_neg_one
#print axioms YMGap.Continuum.RCPositiveContractionOneStep.three_moment
#print axioms YMGap.Continuum.RCPositiveContractionOneStep.oneStep_contraction
