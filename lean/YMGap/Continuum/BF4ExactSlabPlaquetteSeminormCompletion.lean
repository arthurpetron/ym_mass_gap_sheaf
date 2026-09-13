/-
# Explicit-modulus completion carrier for ORIGINAL reflected plaquette distance

The squared distance is exactly E(theta(p-q)*(p-q)). Positivity of the
difference form supplies the sqrt-free triangle inequality. The already
proved radical theorem supplies null congruence. These construct the
existing SquaredSeminorm interface, its modulated Cauchy carrier and the
embedding of the actual positive-definite plaquette null quotient.

This module constructs the completion carrier and embedding, not yet a
completed inner product, its Hilbert-space laws, an observable action,
inter-slab maps, physical transfer, stationary vacuum or a mass gap.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
import YMGap.Continuum.CRealSeminormCompletion

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectedForm
open YMGap.Continuum.BF4ExactSlabPlaquetteNullQuotient
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation

private theorem neg_num (a : Q') : (-a).num = -a.num := rfl

private theorem rc_add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => QPoly.q_add_zero_eqv (A.approx n)))

private theorem rc_distance_symm (a b c : RC) :
    RCsub (RCsub a b) (RCsub b c) = RCsub (RCsub c b) (RCsub b a) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv ((A.approx n + -B.approx n) + -(B.approx n + -C.approx n))
    ((C.approx n + -B.approx n) + -(B.approx n + -A.approx n))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

private theorem rc_parallelogram (a b c : RC) :
    RCadd (RCadd (RCadd a b) (RCadd b c)) (RCsub (RCsub a b) (RCsub b c)) =
      RCadd (RCadd a a) (RCadd c c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  change Q'.eqv (((A.approx n + B.approx n) + (B.approx n + C.approx n)) +
    ((A.approx n + -B.approx n) + -(B.approx n + -C.approx n)))
    ((A.approx n + A.approx n) + (C.approx n + C.approx n))
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.neg_den, neg_num]
  simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
    Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  omega

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {half : Nat}

def distSq (e f : PlaquetteExpression half) : CReal := form w hw0 hw1 (subtract e f) (subtract e f)

theorem distSq_reflected (e f : PlaquetteExpression half) :
    Equiv (distSq w hw0 hw1 e f)
      (expectation w hw0 hw1 half
        (polyMul
          (reflectCorrectedSlabPolynomial (centralExtent half)
            (lower (subtract e f))) (lower (subtract e f)))) :=
  form_reflected w hw0 hw1 (subtract e f) (subtract e f)

theorem distSq_refl (e : PlaquetteExpression half) : Equiv (distSq w hw0 hw1 e e) czero :=
  Quotient.exact ((null_iff_pairing w hw0 hw1 e e).mpr (fun _ => rfl))

theorem distSq_symm (e f : PlaquetteExpression half) : Equiv (distSq w hw0 hw1 e f) (distSq w hw0 hw1 f e) := by
  apply Quotient.exact (s := crealSetoid)
  change pairing w hw0 hw1 (subtract e f) (subtract e f) = pairing w hw0 hw1 (subtract f e) (subtract f e)
  rw [RCBilinearDifference.difference_diagonal subtract (pairing w hw0 hw1)
    (pairing_sub_left w hw0 hw1) (pairing_symm w hw0 hw1) e f]
  rw [RCBilinearDifference.difference_diagonal subtract (pairing w hw0 hw1)
    (pairing_sub_left w hw0 hw1) (pairing_symm w hw0 hw1) f e]
  rw [pairing_symm w hw0 hw1 f e]
  exact rc_distance_symm _ _ _

theorem distSq_nonnegative (e f : PlaquetteExpression half) : leEv czero (distSq w hw0 hw1 e f) :=
  form_nonnegative w hw0 hw1 (subtract e f)

theorem pairing_add_bound (e f : PlaquetteExpression half) :
    RCle (pairing w hw0 hw1 (.add e f) (.add e f))
      (RCadd (RCadd (pairing w hw0 hw1 e e) (pairing w hw0 hw1 e e))
        (RCadd (pairing w hw0 hw1 f f) (pairing w hw0 hw1 f f))) := by
  have h := RCadd_le_add (RCle_refl (pairing w hw0 hw1 (.add e f) (.add e f)))
    (pairing_nonnegative w hw0 hw1 (subtract e f))
  rw [rc_add_zero] at h
  rw [pairing_add_left, pairing_add_right, pairing_add_right,
    RCBilinearDifference.difference_diagonal subtract (pairing w hw0 hw1)
      (pairing_sub_left w hw0 hw1) (pairing_symm w hw0 hw1) e f,
    pairing_symm w hw0 hw1 f e, rc_parallelogram] at h
  rw [pairing_add_left, pairing_add_right, pairing_add_right, pairing_symm w hw0 hw1 f e]
  exact h

theorem distSq_triangle (e f g : PlaquetteExpression half) :
    leEv (distSq w hw0 hw1 e g)
      (CReal.add (CReal.add (distSq w hw0 hw1 e f) (distSq w hw0 hw1 e f))
        (CReal.add (distSq w hw0 hw1 f g) (distSq w hw0 hw1 f g))) := by
  have he : expressionEqv (.add (subtract e f) (subtract f g)) (subtract e g) :=
    (finiteGNSData w (Q'.le_of_lt hw0) 0 half).sub_add_sub e f g
  have h := pairing_add_bound w hw0 hw1 (subtract e f) (subtract f g)
  rw [pairing_congr w hw0 hw1 he he] at h
  exact h

theorem distSq_null_congr {e e' f f' : PlaquetteExpression half}
    (he : Equiv (distSq w hw0 hw1 e e') czero) (hf : Equiv (distSq w hw0 hw1 f f') czero) :
    Equiv (distSq w hw0 hw1 e f) (distSq w hw0 hw1 e' f') := by
  have he' : Null w hw0 hw1 e e' := Quotient.sound he
  have hf' : Null w hw0 hw1 f f' := Quotient.sound hf
  apply Quotient.exact (s := crealSetoid)
  change pairing w hw0 hw1 (subtract e f) (subtract e f) = pairing w hw0 hw1 (subtract e' f') (subtract e' f')
  exact pairing_null_congr w hw0 hw1 (null_add w hw0 hw1 he' (null_smul w hw0 hw1 (-1) hf'))
    (null_add w hw0 hw1 he' (null_smul w hw0 hw1 (-1) hf'))

def seminorm (half : Nat) : SquaredSeminorm where
  Carrier := PlaquetteExpression half
  distSq := distSq w hw0 hw1
  distSq_refl := distSq_refl w hw0 hw1
  distSq_symm := distSq_symm w hw0 hw1
  distSq_nonneg := distSq_nonnegative w hw0 hw1
  distSq_triangle := distSq_triangle w hw0 hw1
  null_congr := distSq_null_congr w hw0 hw1

def Completion (half : Nat) : Type := (seminorm w hw0 hw1 half).Completion

def embedExpression (e : PlaquetteExpression half) : Completion w hw0 hw1 half :=
  (seminorm w hw0 hw1 half).embedRep e

def embedQuotient : Carrier w hw0 hw1 half → Completion w hw0 hw1 half :=
  Quotient.lift (embedExpression w hw0 hw1)
    (fun _ _ h => (seminorm w hw0 hw1 half).embedRep_eq_of_null (Quotient.exact h))

theorem embedQuotient_embed (e : PlaquetteExpression half) :
    embedQuotient w hw0 hw1 (embed w hw0 hw1 e) = embedExpression w hw0 hw1 e := rfl

theorem embedExpression_eq_iff (e f : PlaquetteExpression half) :
    embedExpression w hw0 hw1 e = embedExpression w hw0 hw1 f ↔ Null w hw0 hw1 e f := by
  constructor
  · intro h
    rcases Quotient.exact h with ⟨hc⟩
    have hu : leEv (distSq w hw0 hw1 e f) czero := by
      intro epsilon he
      have hhalf := ExpNeg.half_mul_pos epsilon he
      have hd := hc.close (HalfPow.half * epsilon) hhalf (hc.modulus (HalfPow.half * epsilon)) (Nat.le_refl _)
      obtain ⟨N, hN⟩ := hd (HalfPow.half * epsilon) hhalf
      refine ⟨N, fun n hn => ?_⟩
      exact Q'.le_trans' _ _ _ (hN n hn)
        (Q'.le_of_eqv (Q'.eqv_trans _ _ _ (ExpNeg.two_halves epsilon) (Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' epsilon)))))
    exact Quotient.sound (CReal.equiv_of_leEv_leEv hu (distSq_nonnegative w hw0 hw1 e f))
  · intro h
    exact (seminorm w hw0 hw1 half).embedRep_eq_of_null (Quotient.exact h)

theorem embedQuotient_injective (x y : Carrier w hw0 hw1 half)
    (h : embedQuotient w hw0 hw1 x = embedQuotient w hw0 hw1 y) : x = y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro e f h
  exact Quotient.sound ((embedExpression_eq_iff w hw0 hw1 e f).mp h)

def completedUnit (half : Nat) : Completion w hw0 hw1 half := embedExpression w hw0 hw1 .unit

def completedZero (half : Nat) : Completion w hw0 hw1 half := embedExpression w hw0 hw1 (zeroExpression half)

theorem completedUnit_ne_zero (half : Nat) : completedUnit w hw0 hw1 half ≠ completedZero w hw0 hw1 half := by
  intro h
  exact unit_ne_zero w hw0 hw1 half (embedQuotient_injective w hw0 hw1 (unit w hw0 hw1 half) (zero w hw0 hw1 half) h)

end YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_reflected
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_refl
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_symm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.pairing_add_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_triangle
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.distSq_null_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.seminorm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.Completion
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.embedExpression
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.embedQuotient
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.embedQuotient_embed
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.embedExpression_eq_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.embedQuotient_injective
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.completedUnit
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.completedZero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSeminormCompletion.completedUnit_ne_zero
