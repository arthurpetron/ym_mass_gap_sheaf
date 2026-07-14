/-
# Finite Hermite synthesis and Gaussian sum of squares

Finite coefficient lists are synthesized in the exact Hermite family.  The
Gaussian pairing diagonalizes to the explicit derived sum

  sum_n c_n^2 n!.

Consequently every finite Hermite synthesis has nonnegative Gaussian square.
-/

import YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.SU2QuaternionGaussianHermiteSOS

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionGaussianPolynomialIBP
open YMGap.Continuum.SU2QuaternionGaussianHermite
open YMGap.Continuum.SU2QuaternionGaussianHermiteOrthogonality

local infix:50 " ≈ " => Q'.eqv

set_option maxHeartbeats 800000
set_option maxRecDepth 10000

private theorem neg_num_cast (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             ac_rfl))

theorem gaussianPair_padd_right (p q r : Poly) :
    gaussianPair p (padd q r) ≈ gaussianPair p q + gaussianPair p r := by
  refine Q'.eqv_trans _
    (gaussianExpectation (padd (pmul p q) (pmul p r))) _
    (gaussianExpectation_polyEqv (pmul_padd p q r)) ?_
  exact gaussianExpectation_padd _ _

theorem gaussianPair_padd_left (p q r : Poly) :
    gaussianPair (padd p q) r ≈ gaussianPair p r + gaussianPair q r := by
  refine Q'.eqv_trans _ (gaussianPair r (padd p q)) _
    (gaussianPair_symm _ _) ?_
  refine Q'.eqv_trans _ (gaussianPair r p + gaussianPair r q) _
    (gaussianPair_padd_right r p q) ?_
  exact QPoly.q_add_congr (gaussianPair_symm r p) (gaussianPair_symm r q)

theorem gaussianPair_pscale_right (a : Q') (p q : Poly) :
    gaussianPair p (pscale a q) ≈ a * gaussianPair p q := by
  refine Q'.eqv_trans _ (gaussianPair (pscale a q) p) _
    (gaussianPair_symm _ _) ?_
  refine Q'.eqv_trans _ (a * gaussianPair q p) _
    (gaussianPair_pscale_left a q p) ?_
  exact Q'.mul_eqv_congr_left a _ _ (gaussianPair_symm q p)

/-- Finite Hermite synthesis beginning at mode `n`. -/
def hermiteSynthesisFrom : Nat → List Q' → Poly
  | _, [] => []
  | n, c :: cs =>
      padd (pscale c (hermite n)) (hermiteSynthesisFrom (n + 1) cs)

/-- Explicit diagonal Hermite pairing beginning at mode `n`. -/
def hermiteDiagonalFrom : Nat → List Q' → List Q' → Q'
  | _, [], _ => 0
  | _, _, [] => 0
  | n, c :: cs, d :: ds =>
      (c * d) * Q'.ofNat (hermiteFactorial n) +
        hermiteDiagonalFrom (n + 1) cs ds

private theorem hermite_tail_cross_zero {n start : Nat} (hns : n < start) :
    ∀ cs : List Q',
      gaussianPair (hermite n) (hermiteSynthesisFrom start cs) ≈ 0
  | [] => gaussianPair_zero_right _
  | c :: cs => by
      refine Q'.eqv_trans _
        (gaussianPair (hermite n) (pscale c (hermite start)) +
          gaussianPair (hermite n) (hermiteSynthesisFrom (start + 1) cs)) _
        (gaussianPair_padd_right _ _ _) ?_
      refine Q'.eqv_trans _
        (c * gaussianPair (hermite n) (hermite start) +
          gaussianPair (hermite n) (hermiteSynthesisFrom (start + 1) cs)) _
        (Q'.add_eqv_congr_right _ _ _
          (gaussianPair_pscale_right c (hermite n) (hermite start))) ?_
      refine Q'.eqv_trans _ (c * 0 + 0) _
        (QPoly.q_add_congr
          (Q'.mul_eqv_congr_left c _ _
            (hermite_cross_zero n start (Nat.ne_of_lt hns)))
          (hermite_tail_cross_zero (Nat.lt_succ_of_lt hns) cs)) ?_
      exact Q'.eqv_trans _ (0 + 0) _
        (Q'.add_eqv_congr_right _ _ _ (QPoly.q_mul_zero c))
        (QPoly.q_zero_add_eqv 0)

theorem hermiteSynthesis_pair : ∀ (n : Nat) (cs ds : List Q'),
    gaussianPair (hermiteSynthesisFrom n cs) (hermiteSynthesisFrom n ds) ≈
      hermiteDiagonalFrom n cs ds
  | _, [], _ => gaussianPair_zero_left _
  | _, _ :: _, [] => gaussianPair_zero_right _
  | n, c :: cs, d :: ds => by
      let A := pscale c (hermite n)
      let B := pscale d (hermite n)
      let C := hermiteSynthesisFrom (n + 1) cs
      let D := hermiteSynthesisFrom (n + 1) ds
      have hAB : gaussianPair A B ≈
          (c * d) * Q'.ofNat (hermiteFactorial n) := by
        refine Q'.eqv_trans _ (c * gaussianPair (hermite n) B) _
          (gaussianPair_pscale_left c (hermite n) B) ?_
        refine Q'.eqv_trans _
          (c * (d * gaussianPair (hermite n) (hermite n))) _
          (Q'.mul_eqv_congr_left c _ _
            (gaussianPair_pscale_right d (hermite n) (hermite n))) ?_
        refine Q'.eqv_trans _
          (c * (d * Q'.ofNat (hermiteFactorial n))) _
          (Q'.mul_eqv_congr_left c _ _
            (Q'.mul_eqv_congr_left d _ _ (hermite_norm_factorial n))) ?_
        exact Q'.eqv_symm
          (Q'.mul_assoc_eqv c d (Q'.ofNat (hermiteFactorial n)))
      have hAD : gaussianPair A D ≈ 0 :=
        Q'.eqv_trans _ (c * gaussianPair (hermite n) D) _
          (gaussianPair_pscale_left c (hermite n) D)
          (Q'.eqv_trans _ (c * 0) _
            (Q'.mul_eqv_congr_left c _ _
              (hermite_tail_cross_zero (Nat.lt_succ_self n) ds))
            (QPoly.q_mul_zero c))
      have hCB : gaussianPair C B ≈ 0 :=
        Q'.eqv_trans _ (gaussianPair B C) _ (gaussianPair_symm C B)
          (Q'.eqv_trans _ (d * gaussianPair (hermite n) C) _
            (gaussianPair_pscale_left d (hermite n) C)
            (Q'.eqv_trans _ (d * 0) _
              (Q'.mul_eqv_congr_left d _ _
                (hermite_tail_cross_zero (Nat.lt_succ_self n) cs))
              (QPoly.q_mul_zero d)))
      refine Q'.eqv_trans _
        (gaussianPair A (padd B D) + gaussianPair C (padd B D)) _
        (gaussianPair_padd_left A C (padd B D)) ?_
      refine Q'.eqv_trans _
        ((gaussianPair A B + gaussianPair A D) +
          (gaussianPair C B + gaussianPair C D)) _
        (QPoly.q_add_congr
          (gaussianPair_padd_right A B D)
          (gaussianPair_padd_right C B D)) ?_
      refine Q'.eqv_trans _
        ((((c * d) * Q'.ofNat (hermiteFactorial n)) + 0) +
          (0 + hermiteDiagonalFrom (n + 1) cs ds)) _
        (QPoly.q_add_congr (QPoly.q_add_congr hAB hAD)
          (QPoly.q_add_congr hCB (hermiteSynthesis_pair (n + 1) cs ds))) ?_
      change
        ((((c * d) * Q'.ofNat (hermiteFactorial n)) + 0) +
          (0 + hermiteDiagonalFrom (n + 1) cs ds)) ≈
          (c * d) * Q'.ofNat (hermiteFactorial n) +
            hermiteDiagonalFrom (n + 1) cs ds
      exact QPoly.q_add_congr
        (QPoly.q_add_zero_eqv _)
        (QPoly.q_zero_add_eqv _)

private theorem zero_le_ofNat_local (n : Nat) :
    (0 : Q') ≤ Q'.ofNat n := by
  rw [Q'.zero_le_iff_num_nonneg]
  exact Int.natCast_nonneg _

theorem hermiteDiagonal_self_nonneg : ∀ (n : Nat) (cs : List Q'),
    (0 : Q') ≤ hermiteDiagonalFrom n cs cs
  | _, [] => Q'.le_refl' 0
  | n, c :: cs => by
      exact Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (q_mul_self_nonneg c)
          (zero_le_ofNat_local (hermiteFactorial n)))
        (hermiteDiagonal_self_nonneg (n + 1) cs)

/-- **Every finite Hermite synthesis has a nonnegative Gaussian square.** -/
theorem hermiteSynthesis_square_nonneg (n : Nat) (cs : List Q') :
    (0 : Q') ≤
      gaussianPair (hermiteSynthesisFrom n cs) (hermiteSynthesisFrom n cs) := by
  have heq := hermiteSynthesis_pair n cs cs
  exact Q'.le_trans' _ _ _ (hermiteDiagonal_self_nonneg n cs)
    (Q'.le_of_eqv (Q'.eqv_symm heq))

end YMGap.Continuum.SU2QuaternionGaussianHermiteSOS

#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteSOS.hermiteSynthesis_pair
#print axioms YMGap.Continuum.SU2QuaternionGaussianHermiteSOS.hermiteSynthesis_square_nonneg
