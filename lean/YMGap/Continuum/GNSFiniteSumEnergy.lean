/-
# Sharp finite-sum energy bound on the existing GNS completion

The inequality ||sum x_i||^2 <= n * sum ||x_i||^2 is proved from the
nonnegative squares ||x_i-x_j||^2. No square roots, representatives selected
by choice, finite-dimensional reduction, or extra analytic premise occurs.

This is the finite-vector estimate needed for the neighboring correction
lists in a bounded-degree conditional sweep. It is not itself a sweep
contraction or an interacting coercivity theorem.
-/

import YMGap.Continuum.GNSProjectionSweep
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.GNSFiniteSumEnergy

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.GNSProjectionSweep
open YMGap.Continuum.RingNormaliser

private theorem add_zero (a : RC) : RCadd a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.add_zero' (A.approx n))))

private theorem zero_add (a : RC) : RCadd RCzero a = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
    (fun n => Q'.eqv_of_eq (Q'.zero_add' (A.approx n))))

private theorem sub_zero (a : RC) : RCsub a RCzero = a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _ (by decide : Q'.eqv (-0) 0))
      (Q'.eqv_of_eq (Q'.add_zero' (A.approx n)))))

private theorem scale_zero (a : RC) : RCscale 0 a = RCzero := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n => Q'.zero_mul_eqv _))

private theorem scale_ofNat_zero (a : RC) : RCscale (Q'.ofNat 0) a = RCzero :=
  scale_zero a

private theorem scale_succ (n : Nat) (a : RC) :
    RCscale (Q'.ofNat (n+1)) a = RCadd (RCscale (Q'.ofNat n) a) a := by
  refine Quotient.inductionOn a ?_
  intro A
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun k =>
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv n 1))
      (Q'.eqv_trans _ _ _ (Q'.add_mul_eqv _ _ _)
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv _)))))

private theorem add_nonneg {a b : RC} (ha : RCnonneg a) (hb : RCnonneg b) :
    RCnonneg (RCadd a b) := by
  have h := RCadd_le_add ha hb
  rw [zero_add] at h
  exact h

private theorem le_of_sub_nonneg {a b : RC} (h : RCnonneg (RCsub b a)) :
    RCle a b := by
  have he : RCadd (RCsub b a) a = b := by
    refine Quotient.inductionOn₂ b a ?_
    intro B A
    exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv
      (fun n => Q'.sub_add_cancel_eqv _ _))
  have hs := RCadd_le_add h (RCle_refl a)
  rw [zero_add, he] at hs
  exact hs

private theorem row_step (n : Q') (a b e c d : RC) :
    RCsub
      (RCadd (RCadd (RCscale n a) a) (RCadd b e))
      (RCadd (RCadd c d) (RCadd c d)) =
    RCadd (RCsub (RCsub a c) (RCsub c b))
      (RCsub (RCadd (RCscale n a) e) (RCadd d d)) := by
  refine Quotient.inductionOn₃ a b e ?_
  intro A B E
  refine Quotient.inductionOn₂ c d ?_
  intro C D
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact poly_identity_of_normal_eq
    (.add (.add (.add (.mul (.var 0) (.var 1)) (.var 1)) (.add (.var 2) (.var 3)))
      (.neg (.add (.add (.var 4) (.var 5)) (.add (.var 4) (.var 5)))))
    (.add (.add (.add (.var 1) (.neg (.var 4))) (.neg (.add (.var 4) (.neg (.var 2)))))
      (.add (.add (.mul (.var 0) (.var 1)) (.var 3)) (.neg (.add (.var 5) (.var 5)))))
    (by decide) (fun
      | 0 => n
      | 1 => A.approx k
      | 2 => B.approx k
      | 3 => E.approx k
      | 4 => C.approx k
      | _ => D.approx k)

private theorem deficit_step (n : Q') (a b c d : RC) :
    RCsub (RCadd (RCscale n (RCadd a b)) (RCadd a b))
      (RCadd (RCadd a d) (RCadd d c)) =
    RCadd (RCsub (RCscale n b) c)
      (RCsub (RCadd (RCscale n a) b) (RCadd d d)) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro A B C
  refine Quotient.inductionOn d ?_
  intro E
  apply Quotient.sound
  apply SumOfSquares.Equiv_of_approx_eqv
  intro k
  exact poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.add (.var 1) (.var 2))) (.add (.var 1) (.var 2)))
      (.neg (.add (.add (.var 1) (.var 4)) (.add (.var 4) (.var 3)))))
    (.add (.add (.mul (.var 0) (.var 2)) (.neg (.var 3)))
      (.add (.add (.mul (.var 0) (.var 1)) (.var 2)) (.neg (.add (.var 4) (.var 4)))))
    (by decide) (fun
      | 0 => n
      | 1 => A.approx k
      | 2 => B.approx k
      | 3 => C.approx k
      | _ => E.approx k)

variable {D : GNSData}

/-- Actual finite addition on the original completion. -/
def vectorSum : List (GNSCompletionSpace D) → GNSCompletionSpace D
  | [] => embedV D D.zero
  | x :: xs => D.cAdd x (vectorSum xs)

def energy : List (GNSCompletionSpace D) → RC
  | [] => RCzero
  | x :: xs => RCadd (normSq x) (energy xs)

/-- Sum of all unordered pairwise squared differences, with list multiplicity. -/
def pairEnergy : List (GNSCompletionSpace D) → RC
  | [] => RCzero
  | x :: xs => RCadd (pairEnergy xs) (energy (xs.map (D.cSub x)))

private theorem norm_add (x y : GNSCompletionSpace D) :
    normSq (D.cAdd x y) =
      RCadd (RCadd (normSq x) (D.cinnerCompl x y))
        (RCadd (D.cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [D.cinnerCompl_cAdd_left, D.cinnerCompl_cAdd_right,
    D.cinnerCompl_cAdd_right, D.cinnerCompl_comm y x]

private theorem norm_sub (x y : GNSCompletionSpace D) :
    normSq (D.cSub x y) =
      RCsub (RCsub (normSq x) (D.cinnerCompl x y))
        (RCsub (D.cinnerCompl x y) (normSq y)) := by
  unfold normSq
  rw [D.cinnerCompl_cSub_left, D.cinnerCompl_comm x (D.cSub x y),
    D.cinnerCompl_cSub_left, D.cinnerCompl_comm y (D.cSub x y),
    D.cinnerCompl_cSub_left, D.cinnerCompl_comm y x]

theorem energy_nonneg (xs : List (GNSCompletionSpace D)) : RCnonneg (energy xs) := by
  induction xs with
  | nil => exact RCle_refl _
  | cons x xs ih => exact add_nonneg (D.cinner_self_nonneg x) ih

theorem pairEnergy_nonneg (xs : List (GNSCompletionSpace D)) : RCnonneg (pairEnergy xs) := by
  induction xs with
  | nil => exact RCle_refl _
  | cons x xs ih => exact add_nonneg ih (energy_nonneg _)

/-- Exact row of the Gram-defect identity, valid without any sign choice. -/
theorem difference_energy (x : GNSCompletionSpace D) (xs : List (GNSCompletionSpace D)) :
    energy (xs.map (D.cSub x)) =
      RCsub (RCadd (RCscale (Q'.ofNat xs.length) (normSq x)) (energy xs))
        (RCadd (D.cinnerCompl x (vectorSum xs)) (D.cinnerCompl x (vectorSum xs))) := by
  induction xs with
  | nil =>
      simp only [List.map_nil, List.length_nil, energy, vectorSum,
        D.cinnerCompl_embedZero_right, scale_ofNat_zero, zero_add, sub_zero]
  | cons y xs ih =>
      simp only [List.map_cons, List.length_cons, energy, vectorSum]
      rw [norm_sub, ih, D.cinnerCompl_cAdd_right, scale_succ]
      exact (row_step _ _ _ _ _ _).symm

/-- Exact finite Gram identity. The entire deficit is a constructed sum of
nonnegative pairwise squares, not an assumed Cauchy--Schwarz bound. -/
theorem energy_deficit (xs : List (GNSCompletionSpace D)) :
    RCsub (RCscale (Q'.ofNat xs.length) (energy xs)) (normSq (vectorSum xs)) =
      pairEnergy xs := by
  induction xs with
  | nil =>
      simp only [List.length_nil, vectorSum, energy, pairEnergy, normSq,
        D.cinnerCompl_embedZero_left, scale_ofNat_zero, sub_zero]
  | cons x xs ih =>
      simp only [List.length_cons, energy, vectorSum, pairEnergy]
      rw [norm_add, scale_succ, deficit_step, ih, difference_energy]

/-- Sharp length factor on ALL completed vectors, including the empty list. -/
theorem norm_vectorSum_le (xs : List (GNSCompletionSpace D)) :
    RCle (normSq (vectorSum xs)) (RCscale (Q'.ofNat xs.length) (energy xs)) := by
  apply le_of_sub_nonneg
  rw [energy_deficit]
  exact pairEnergy_nonneg xs

/-- A supplied geometric list-length bound gives a numerical coefficient;
the energy is still evaluated on the actual listed completed vectors. -/
theorem norm_vectorSum_le_of_length (xs : List (GNSCompletionSpace D))
    (bound : Nat) (hbound : xs.length ≤ bound) :
    RCle (normSq (vectorSum xs)) (RCscale (Q'.ofNat bound) (energy xs)) :=
  RCle_trans (norm_vectorSum_le xs)
    (RCscale_scalar_mono (ofNat_le_ofNat hbound) (energy_nonneg xs))

#print axioms energy_nonneg
#print axioms pairEnergy_nonneg
#print axioms difference_energy
#print axioms energy_deficit
#print axioms norm_vectorSum_le
#print axioms norm_vectorSum_le_of_length

end YMGap.Continuum.GNSFiniteSumEnergy
