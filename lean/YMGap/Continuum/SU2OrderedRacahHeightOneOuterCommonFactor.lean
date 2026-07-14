/-
# Common-factor form of the outer coordinate-two polynomial

The coordinate-two row is factored over the common order-`k-2` falling
factorials.  Its remaining scalar is a division-free quadratic in the four
omitted trailing factors.  This is the form compatible with the established
coordinate-one and coordinate-zero scaling identities.
-/

import YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial

namespace YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor

open YMGap.Constructive
open YMGap.Continuum.SU2TransvectantMixedPentagon
open YMGap.Continuum.SU2TransvectantFactorialRecurrence
open YMGap.Continuum.SU2OrderedRacahOmegaCorrectionGuardedHahn
open YMGap.Continuum.SU2OrderedRacahHeightOneOuterClosedPolynomial

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num (q : Q') : (-q).num = -q.num := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num, Int.add_mul, Int.mul_add,
               Int.neg_mul, Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one, Int.zero_mul, Int.mul_zero]; try ac_rfl))

private theorem mul_eqv_congr {a b c d : Q'}
    (hab : a ≈ b) (hcd : c ≈ d) : a * c ≈ b * d :=
  Q'.eqv_trans _ (b * c) _
    (Q'.mul_eqv_congr_right _ _ _ hab)
    (Q'.mul_eqv_congr_left _ _ _ hcd)

/-- The explicit scalar left after extracting the common order-`k-2`
falling-factorial carrier. -/
def outerSecondTwoScalar (m n k i : Nat) : Q' :=
  (Q'.ofNat (i - k + 2) * Q'.ofNat (i - k + 1)) *
      (Q'.ofNat (n - k) * Q'.ofNat (n - k - 1)) +
    -(tvBinomQ k 1 * Q'.ofNat (i - k + 2) * Q'.ofNat (m - i) *
      Q'.ofNat 2 * Q'.ofNat (n - k)) +
    tvBinomQ k 2 * tvFallQ (m - i) 2 * Q'.ofNat 2

/-- Coordinate-one scalar after extracting the same order-`k-2` base. -/
def outerSecondOneScalarAtTwoBase (m n k i : Nat) : Q' :=
  (Q'.ofNat (i - k + 2) * Q'.ofNat (n - 1)) *
    (Q'.ofNat (i - k + 1) * Q'.ofNat (n - k) +
      -(Q'.ofNat k * Q'.ofNat (m - i)))

/-- Coordinate-zero scalar after extracting the same order-`k-2` base. -/
def outerSecondZeroScalarAtTwoBase (n k i : Nat) : Q' :=
  (Q'.ofNat (i - k + 2) * Q'.ofNat (i - k + 1)) *
    (Q'.ofNat n * Q'.ofNat (n - 1))

/-- **Coordinate-two common-factor identity.** -/
theorem outerSecondTwoClosedPolynomial_factored
    (m n k i : Nat) (hk : 2 ≤ k) (hki : k ≤ i) (hkn : k + 2 ≤ n) :
    outerSecondTwoClosedPolynomial m n k i ≈
      (tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) *
        outerSecondTwoScalar m n k i := by
  let I := tvFallQ i (k - 2)
  let N := tvFallQ (n - 2) (k - 2)
  let A := Q'.ofNat (i - k + 2)
  let B := Q'.ofNat (i - k + 1)
  let C := Q'.ofNat (n - k)
  let D := Q'.ofNat (n - k - 1)
  let M := Q'.ofNat (m - i)
  let T0 := (A * B) * (C * D)
  let T1 := -(tvBinomQ k 1 * A * M * Q'.ofNat 2 * C)
  let T2 := tvBinomQ k 2 * tvFallQ (m - i) 2 * Q'.ofNat 2
  have hi1 := tvFallQ_trailing_shift i (k - 2) (by omega)
  have hi1' : I * A ≈ tvFallQ i (k - 1) := by
    simpa only [I, A, show i - (k - 2) = i - k + 2 by omega,
      show k - 2 + 1 = k - 1 by omega] using hi1
  have hi2 := tvFallQ_trailing_shift i (k - 1) (by omega)
  have hi2' : tvFallQ i (k - 1) * B ≈ tvFallQ i k := by
    simpa only [B, show i - (k - 1) = i - k + 1 by omega,
      show k - 1 + 1 = k by omega] using hi2
  have hi : (I * A) * B ≈ tvFallQ i k :=
    Q'.eqv_trans _ (tvFallQ i (k - 1) * B) _
      (Q'.mul_eqv_congr_right _ _ _ hi1') hi2'
  have hn1 := tvFallQ_trailing_shift (n - 2) (k - 2) (by omega)
  have hn1' : N * C ≈ tvFallQ (n - 2) (k - 1) := by
    simpa only [N, C, show n - 2 - (k - 2) = n - k by omega,
      show k - 2 + 1 = k - 1 by omega] using hn1
  have hn2 := tvFallQ_trailing_shift (n - 2) (k - 1) (by omega)
  have hn2' : tvFallQ (n - 2) (k - 1) * D ≈
      tvFallQ (n - 2) k := by
    simpa only [D, show n - 2 - (k - 1) = n - k - 1 by omega,
      show k - 1 + 1 = k by omega] using hn2
  have hn : (N * C) * D ≈ tvFallQ (n - 2) k :=
    Q'.eqv_trans _ (tvFallQ (n - 2) (k - 1) * D) _
      (Q'.mul_eqv_congr_right _ _ _ hn1') hn2'
  have hterm0 : tvFallQ i k * tvFallQ (n - 2) k ≈ (I * N) * T0 := by
    refine Q'.eqv_trans _ (((I * A) * B) * ((N * C) * D)) _
      (by
        exact Q'.eqv_symm (mul_eqv_congr
          hi hn)) ?_
    simp only [I, N, A, B, C, D, T0]
    ring_qeqv
  have hterm1 :
      -(tvBinomQ k 1 * tvFallQ i (k - 1) * M *
          Q'.ofNat 2 * tvFallQ (n - 2) (k - 1)) ≈
        (I * N) * T1 := by
    refine Q'.eqv_trans _
      (-(tvBinomQ k 1 * (I * A) * M * Q'.ofNat 2 * (N * C))) _ ?_ ?_
    · exact Q'.neg_eqv_congr _ _
        (mul_eqv_congr
          (mul_eqv_congr
            (mul_eqv_congr
              (Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hi1'))
              (Q'.eqv_refl M))
            (Q'.eqv_refl (Q'.ofNat 2)))
          (Q'.eqv_symm hn1'))
    · simp only [I, N, A, C, M, T1]
      ring_qeqv
  have hterm2 :
      tvBinomQ k 2 * tvFallQ i (k - 2) * tvFallQ (m - i) 2 *
          Q'.ofNat 2 * tvFallQ (n - 2) (k - 2) ≈
        (I * N) * T2 := by
    simp only [I, N, T2]
    ring_qeqv
  unfold outerSecondTwoClosedPolynomial
  refine Q'.eqv_trans _ ((I * N) * T0 + (I * N) * T1 + (I * N) * T2) _
    (Q'.add_eqv_congr' (Q'.add_eqv_congr' hterm0 hterm1) hterm2) ?_
  simp only [I, N, T0, T1, T2, outerSecondTwoScalar, A, B, C, D, M]
  refine Q'.eqv_symm (Q'.eqv_trans _
    ((tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) * (T0 + T1) +
      (tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) * T2) _
    (Q'.mul_add_eqv _ _ _) ?_)
  exact Q'.add_eqv_congr_right _ _ _ (Q'.mul_add_eqv _ _ _)

/-- The arbitrary-order coordinate-two coefficient in common-factor form. -/
theorem transvectFactorialCoeff_second_two_factored
    (m n k i : Nat) (hk : 2 ≤ k) (hki : k ≤ i) (hkn : k + 2 ≤ n) :
    transvectFactorialCoeff m n k i 2 ≈
      (tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) *
        outerSecondTwoScalar m n k i :=
  Q'.eqv_trans _ _ _
    (transvectFactorialCoeff_second_two_closed m n k i hk)
    (outerSecondTwoClosedPolynomial_factored m n k i hk hki hkn)

/-- Coordinate one rewritten over the coordinate-two common base. -/
theorem transvectFactorialCoeff_second_one_at_two_base
    (m n k i : Nat) (hk : 2 ≤ k) (hki : k ≤ i) (hkn : k + 2 ≤ n) :
    transvectFactorialCoeff m n k i 1 ≈
      (tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) *
        outerSecondOneScalarAtTwoBase m n k i := by
  let I := tvFallQ i (k - 2)
  let N := tvFallQ (n - 2) (k - 2)
  let A := Q'.ofNat (i - k + 2)
  let E := Q'.ofNat (n - 1)
  let F := Q'.ofNat (i - k + 1) * Q'.ofNat (n - k) +
    -(Q'.ofNat k * Q'.ofNat (m - i))
  have hi0 := tvFallQ_trailing_shift i (k - 2) (by omega)
  have hi : I * A ≈ tvFallQ i (k - 1) := by
    simpa only [I, A, show i - (k - 2) = i - k + 2 by omega,
      show k - 2 + 1 = k - 1 by omega] using hi0
  have hn0 := tvFallQ_leading_shift (n - 1) (k - 2)
  have hn : E * N ≈ tvFallQ (n - 1) (k - 1) := by
    simpa only [E, N, show n - 1 - 1 = n - 2 by omega,
      show k - 2 + 1 = k - 1 by omega] using hn0
  have hrow := transvectFactorialCoeff_second_one_factored
    m n k i (by omega) hki (by omega)
  refine Q'.eqv_trans _
    ((tvFallQ i (k - 1) * tvFallQ (n - 1) (k - 1)) * F) _
    (by simpa only [F] using hrow) ?_
  refine Q'.eqv_trans _ (((I * A) * (E * N)) * F) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ F
      (mul_eqv_congr (Q'.eqv_symm hi) (Q'.eqv_symm hn))
  · simp only [I, N, A, E, F, outerSecondOneScalarAtTwoBase]
    ring_qeqv

/-- Coordinate zero rewritten over the coordinate-two common base. -/
theorem transvectFactorialCoeff_zero_second_at_two_base
    (m n k i : Nat) (hk : 2 ≤ k) (hki : k ≤ i) (hkn : k + 2 ≤ n) :
    transvectFactorialCoeff m n k i 0 ≈
      (tvFallQ i (k - 2) * tvFallQ (n - 2) (k - 2)) *
        outerSecondZeroScalarAtTwoBase n k i := by
  let I := tvFallQ i (k - 2)
  let N := tvFallQ (n - 2) (k - 2)
  let A := Q'.ofNat (i - k + 2)
  let B := Q'.ofNat (i - k + 1)
  let E := Q'.ofNat (n - 1)
  let G := Q'.ofNat n
  have hi1 := tvFallQ_trailing_shift i (k - 2) (by omega)
  have hi1' : I * A ≈ tvFallQ i (k - 1) := by
    simpa only [I, A, show i - (k - 2) = i - k + 2 by omega,
      show k - 2 + 1 = k - 1 by omega] using hi1
  have hi2 := tvFallQ_trailing_shift i (k - 1) (by omega)
  have hi2' : tvFallQ i (k - 1) * B ≈ tvFallQ i k := by
    simpa only [B, show i - (k - 1) = i - k + 1 by omega,
      show k - 1 + 1 = k by omega] using hi2
  have hi : (I * A) * B ≈ tvFallQ i k :=
    Q'.eqv_trans _ (tvFallQ i (k - 1) * B) _
      (Q'.mul_eqv_congr_right _ _ _ hi1') hi2'
  have hn1 := tvFallQ_leading_shift (n - 1) (k - 2)
  have hn1' : E * N ≈ tvFallQ (n - 1) (k - 1) := by
    simpa only [E, N, show n - 1 - 1 = n - 2 by omega,
      show k - 2 + 1 = k - 1 by omega] using hn1
  have hn2 := tvFallQ_leading_shift n (k - 1)
  have hn2' : G * tvFallQ (n - 1) (k - 1) ≈ tvFallQ n k := by
    simpa only [G, show k - 1 + 1 = k by omega] using hn2
  have hn : G * (E * N) ≈ tvFallQ n k :=
    Q'.eqv_trans _ (G * tvFallQ (n - 1) (k - 1)) _
      (Q'.mul_eqv_congr_left G _ _ hn1') hn2'
  have hrow := transvectFactorialCoeff_zero_second_closed m n k i
  refine Q'.eqv_trans _ (tvFallQ i k * tvFallQ n k) _ hrow ?_
  refine Q'.eqv_trans _ (((I * A) * B) * (G * (E * N))) _ ?_ ?_
  · exact Q'.eqv_symm (mul_eqv_congr hi hn)
  · simp only [I, N, A, B, E, G, outerSecondZeroScalarAtTwoBase]
    ring_qeqv

end YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor

#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor.outerSecondTwoClosedPolynomial_factored
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor.transvectFactorialCoeff_second_two_factored
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor.transvectFactorialCoeff_second_one_at_two_base
#print axioms YMGap.Continuum.SU2OrderedRacahHeightOneOuterCommonFactor.transvectFactorialCoeff_zero_second_at_two_base
