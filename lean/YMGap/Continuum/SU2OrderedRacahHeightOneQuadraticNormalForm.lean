/-
# Integral normal forms for the remaining height-one quadratics

The common-denominator residual still contains only three elementary
factorial atoms: `choose k 1`, `choose k 2`, and the complementary
`choose k (k-2)`, together with order-two falling factorials.  This module
normalizes them to division-free quadratic products.  A single factor two
clears both complementary binomials in the inner height-two polynomial.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneScaledResidualPolynomial
import YMGap.Continuum.SU2TransvectantRisingVandermonde

namespace YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm

set_option maxHeartbeats 2400000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialSeed
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2TransvectantHighestWeightGramFormula
open YMGap.Continuum.SU2TransvectantRisingVandermonde
open YMGap.Continuum.SU2OrderedRacahHeightOneLegacyCancellation
open YMGap.Continuum.SU2OrderedRacahHeightOnePolynomialPropagation
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem ofNat_mul_eqv (a b : Nat) :
    Q'.ofNat a * Q'.ofNat b ≈ Q'.ofNat (a * b) := by
  unfold Q'.eqv
  simp only [Q'.mul_num_cast, Q'.mul_den_cast, Q'.ofNat_num_cast,
    Q'.ofNat_den_cast]
  push_cast
  simp

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

private theorem twice_three_collect
    (T L X R : Q') :
    T * (L + (-X + R)) ≈
      (T * L + -(T * X)) + T * R := by
  ring_qeqv

/-- The order-one factorial binomial is its label. -/
theorem tvBinomQ_one_closed (k : Nat) (hk : 0 < k) :
    tvBinomQ k 1 ≈ Q'.ofNat k := by
  have h := tvBinomQ_mul_fact_eq_fall k 1 (by omega)
  have hf := tvFallQ_one k
  refine Q'.eqv_trans _ (tvBinomQ k 1 * Q'.ofNat (tvFact 1)) _ ?_ ?_
  · simp only [tvFact]
    exact Q'.eqv_symm (Q'.mul_one_eqv _)
  · exact Q'.eqv_trans _ _ _ h hf

/-- Twice the complementary order-two binomial is `k(k-1)`. -/
theorem two_mul_tvBinomQ_complement_two (k : Nat) (hk : 2 ≤ k) :
    Q'.ofNat 2 * tvBinomQ k (k - 2) ≈
      Q'.ofNat k * Q'.ofNat (k - 1) := by
  have hc0 := tvBinomQ_eqv_choose k (k - 2) (by omega)
  have hc2 := tvBinomQ_eqv_choose k 2 hk
  have hs : PNPaths.choose k 2 = PNPaths.choose k (k - 2) := by
    simpa only [show k - 2 = k - 2 by rfl] using choose_symm k 2 hk
  have hcomp : tvBinomQ k (k - 2) ≈ tvBinomQ k 2 :=
    Q'.eqv_trans _ (Q'.ofNat (PNPaths.choose k (k - 2))) _ hc0
      (Q'.eqv_trans _ (Q'.ofNat (PNPaths.choose k 2)) _
        (Q'.eqv_of_eq (congrArg Q'.ofNat hs.symm)) (Q'.eqv_symm hc2))
  have h2 := tvBinomQ_mul_fact_eq_fall k 2 hk
  have hfall := tvFallQ_two k
  refine Q'.eqv_trans _ (tvBinomQ k 2 * Q'.ofNat 2) _ ?_ ?_
  · refine Q'.eqv_trans _ (Q'.ofNat 2 * tvBinomQ k 2) _
      (Q'.mul_eqv_congr_left _ _ _ hcomp) ?_
    ring_qeqv
  · refine Q'.eqv_trans _ (tvBinomQ k 2 * Q'.ofNat (tvFact 2)) _ ?_ ?_
    · exact Q'.eqv_refl _
    refine Q'.eqv_trans _ (tvFallQ k 2) _ h2 ?_
    refine Q'.eqv_trans _ (Q'.ofNat (k * (k - 1))) _ hfall ?_
    exact Q'.eqv_symm (ofNat_mul_eqv k (k - 1))

/-- Integral quadratic obtained from twice the height-two inner scalar. -/
def heightTwoFullPolynomialTwice (m n k j l : Nat) : Q' :=
  (Q'.ofNat l * Q'.ofNat (l - 1)) *
      (Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)) +
    -(Q'.ofNat 2 *
      (Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
        Q'.ofNat (n - k))) +
    (Q'.ofNat j * Q'.ofNat (j - 1)) *
      (Q'.ofNat (m - k) * Q'.ofNat (m - k - 1))

/-- One factor two clears the two complementary binomials in the complete
height-two polynomial. -/
theorem height_two_full_polynomial_twice
    (m n k j l : Nat) (hj : 2 ≤ j) (hl : 2 ≤ l) :
    Q'.ofNat 2 * heightTwoFullPolynomial m n k j l ≈
      heightTwoFullPolynomialTwice m n k j l := by
  let CL := tvBinomQ l (l - 2)
  let CJ := tvBinomQ j (j - 2)
  let L2 := Q'.ofNat l * Q'.ofNat (l - 1)
  let J2 := Q'.ofNat j * Q'.ofNat (j - 1)
  let NL := Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)
  let MJ := Q'.ofNat (m - k) * Q'.ofNat (m - k - 1)
  let LT := CL * Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)
  let RT := CJ * Q'.ofNat (m - k) * Q'.ofNat (m - k - 1)
  let X := Q'.ofNat j * Q'.ofNat l * Q'.ofNat (m - k) *
    Q'.ofNat (n - k)
  have hcl : Q'.ofNat 2 * CL ≈ L2 := by
    simpa only [CL, L2] using two_mul_tvBinomQ_complement_two l hl
  have hcj : Q'.ofNat 2 * CJ ≈ J2 := by
    simpa only [CJ, J2] using two_mul_tvBinomQ_complement_two j hj
  have hlt : Q'.ofNat 2 * LT ≈ L2 * NL := by
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * CL) * NL) _
      (by simp only [LT, NL]; ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ NL hcl
  have hrt : Q'.ofNat 2 * RT ≈ J2 * MJ := by
    refine Q'.eqv_trans _ ((Q'.ofNat 2 * CJ) * MJ) _
      (by simp only [RT, MJ]; ring_qeqv) ?_
    exact Q'.mul_eqv_congr_right _ _ MJ hcj
  unfold heightTwoFullPolynomial heightTwoLeftPolynomial
    heightTwoLegacyPolynomial heightTwoMixedPolynomial
    heightTwoRightPolynomial
  change Q'.ofNat 2 * (LT + (-X + RT)) ≈ _
  refine Q'.eqv_trans _
    ((Q'.ofNat 2 * LT + -(Q'.ofNat 2 * X)) +
      Q'.ofNat 2 * RT) _
    (twice_three_collect (Q'.ofNat 2) LT X RT) ?_
  refine Q'.eqv_trans _
    ((L2 * NL + -(Q'.ofNat 2 * X)) + J2 * MJ) _
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr'
        hlt (Q'.eqv_refl _)) hrt) ?_
  unfold heightTwoFullPolynomialTwice
  simp only [L2, J2, NL, MJ, X]
  exact Q'.eqv_refl _

/-- Integral normal form of the outer coordinate-two scalar. -/
def outerSecondTwoIntegralScalar (m n k i : Nat) : Q' :=
  (Q'.ofNat (i - k + 2) * Q'.ofNat (i - k + 1)) *
      (Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)) +
    -(Q'.ofNat k * Q'.ofNat (i - k + 2) * Q'.ofNat (m - i) *
      Q'.ofNat 2 * Q'.ofNat (n - k)) +
    (Q'.ofNat k * Q'.ofNat (k - 1)) *
      (Q'.ofNat (m - i) * Q'.ofNat (m - i - 1))

/-- The coordinate-two scalar has no residual denominator: its displayed
factor two cancels `choose k 2`. -/
theorem outer_second_two_integral
    (m n k i : Nat) (hk : 2 ≤ k) :
    outerSecondTwoScalar m n k i ≈
      outerSecondTwoIntegralScalar m n k i := by
  let C1 := tvBinomQ k 1
  let C2 := tvBinomQ k 2
  let M2 := tvFallQ (m - i) 2
  let K := Q'.ofNat k
  let K1 := Q'.ofNat (k - 1)
  let M := Q'.ofNat (m - i)
  let M1 := Q'.ofNat (m - i - 1)
  have hc1 : C1 ≈ K := by
    simpa only [C1, K] using tvBinomQ_one_closed k (by omega)
  have hc2 : C2 * Q'.ofNat 2 ≈ K * K1 := by
    refine Q'.eqv_trans _ (Q'.ofNat 2 * C2) _ (by ring_qeqv) ?_
    have h := tvBinomQ_mul_fact_eq_fall k 2 hk
    refine Q'.eqv_trans _ (tvFallQ k 2) _ ?_ ?_
    · exact Q'.eqv_trans _ (C2 * Q'.ofNat 2) _
        (by ring_qeqv) (by simpa only [C2, show tvFact 2 = 2 by decide] using h)
    refine Q'.eqv_trans _ (Q'.ofNat (k * (k - 1))) _ (tvFallQ_two k) ?_
    exact Q'.eqv_symm (ofNat_mul_eqv k (k - 1))
  have hm2 : M2 ≈ M * M1 := by
    refine Q'.eqv_trans _ (Q'.ofNat ((m - i) * (m - i - 1))) _
      (by simpa only [M2] using tvFallQ_two (m - i)) ?_
    exact Q'.eqv_symm (ofNat_mul_eqv (m - i) (m - i - 1))
  unfold outerSecondTwoScalar outerSecondTwoIntegralScalar
  refine Q'.add_eqv_congr'
    (Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.mul_eqv_congr_right _ _ _ hc1)))))) ?_
  refine Q'.eqv_trans _ ((C2 * Q'.ofNat 2) * M2) _
    (by simp only [C2, M2]; ring_qeqv) ?_
  exact mul_eqv_congr hc2 hm2

end YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm.tvBinomQ_one_closed
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm.two_mul_tvBinomQ_complement_two
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm.height_two_full_polynomial_twice
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneQuadraticNormalForm.outer_second_two_integral
