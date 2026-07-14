/-
# Closed form of the outer second-coordinate-two polynomial

The outer height-one row has support at contraction summands `0,1,2`.
This module evaluates their phase and small-coordinate falling factors,
leaving a division-free quadratic in the arbitrary outer coordinate.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2OrderedRacahHeightOneCarrier
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterPolynomial

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero,
               show (1 : Q').num = 1 from rfl,
               show ((1 : Q').den : Int) = 1 from rfl]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- Closed division-free polynomial for an outer row at second coordinate
two. -/
def outerSecondTwoClosedPolynomial (m n k i : Nat) : Q' :=
  (tvFallQ i k * tvFallQ (n - 2) k +
    -(tvBinomQ k 1 * tvFallQ i (k - 1) * Q'.ofNat (m - i) *
      Q'.ofNat 2 * tvFallQ (n - 2) (k - 1))) +
    tvBinomQ k 2 * tvFallQ i (k - 2) * tvFallQ (m - i) 2 *
      Q'.ofNat 2 * tvFallQ (n - 2) (k - 2)

private theorem outer_second_two_term_zero_closed (m n k i : Nat) :
    heightFactorialSummand m n k i 2 0 ≈
      tvFallQ i k * tvFallQ (n - 2) k := by
  have hp : tvPhase 0 ≈ 1 := by decide
  have hb := tvBinomQ_zero k
  have hm := tvFallQ_zero (m - i)
  have h2 := tvFallQ_zero 2
  unfold heightFactorialSummand
  refine Q'.eqv_trans _
    ((1 : Q') * 1 * tvFallQ i k * 1 * 1 * tvFallQ (n - 2) k) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (mul_eqv_congr hp hb) (Q'.eqv_refl _)) hm) h2)
      (Q'.eqv_refl _)
  · ring_qeqv

private theorem outer_second_two_term_one_closed (m n k i : Nat) :
    heightFactorialSummand m n k i 2 1 ≈
      -(tvBinomQ k 1 * tvFallQ i (k - 1) * Q'.ofNat (m - i) *
        Q'.ofNat 2 * tvFallQ (n - 2) (k - 1)) := by
  have hp : tvPhase 1 ≈ -(1 : Q') := by decide
  have hm := tvFallQ_one (m - i)
  have h2 : tvFallQ 2 1 ≈ Q'.ofNat 2 := tvFallQ_one 2
  unfold heightFactorialSummand
  refine Q'.eqv_trans _
    ((-(1 : Q')) * tvBinomQ k 1 * tvFallQ i (k - 1) *
      Q'.ofNat (m - i) * Q'.ofNat 2 *
      tvFallQ (n - 2) (k - 1)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (mul_eqv_congr hp (Q'.eqv_refl _))
            (Q'.eqv_refl _)) hm) h2)
      (Q'.eqv_refl _)
  · ring_qeqv

private theorem outer_second_two_term_two_closed (m n k i : Nat) :
    heightFactorialSummand m n k i 2 2 ≈
      tvBinomQ k 2 * tvFallQ i (k - 2) * tvFallQ (m - i) 2 *
        Q'.ofNat 2 * tvFallQ (n - 2) (k - 2) := by
  have hp : tvPhase 2 ≈ 1 := by decide
  have h2 : tvFallQ 2 2 ≈ Q'.ofNat 2 := by
    simpa only [show 2 * (2 - 1) = 2 by decide] using tvFallQ_two 2
  unfold heightFactorialSummand
  refine Q'.eqv_trans _
    ((1 : Q') * tvBinomQ k 2 * tvFallQ i (k - 2) *
      tvFallQ (m - i) 2 * Q'.ofNat 2 *
      tvFallQ (n - 2) (k - 2)) _ ?_ ?_
  · exact mul_eqv_congr
      (mul_eqv_congr
        (mul_eqv_congr
          (mul_eqv_congr (mul_eqv_congr hp (Q'.eqv_refl _))
            (Q'.eqv_refl _)) (Q'.eqv_refl _)) h2)
      (Q'.eqv_refl _)
  · ring_qeqv

/-- The support polynomial and its closed quadratic form agree exactly. -/
theorem outerSecondTwoPolynomial_closed (m n k i : Nat) :
    outerSecondTwoPolynomial m n k i ≈
      outerSecondTwoClosedPolynomial m n k i := by
  unfold outerSecondTwoPolynomial outerSecondTwoClosedPolynomial
  exact Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (outer_second_two_term_zero_closed m n k i)
      (outer_second_two_term_one_closed m n k i))
    (outer_second_two_term_two_closed m n k i)

/-- Complete arbitrary-order closed outer row. -/
theorem transvectFactorialCoeff_second_two_closed
    (m n k i : Nat) (hk : 2 ≤ k) :
    transvectFactorialCoeff m n k i 2 ≈
      outerSecondTwoClosedPolynomial m n k i :=
  Q'.eqv_trans _ _ _
    (transvectFactorialCoeff_second_two_three_term m n k i hk)
    (outerSecondTwoPolynomial_closed m n k i)

end YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial.outerSecondTwoPolynomial_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial.transvectFactorialCoeff_second_two_closed
