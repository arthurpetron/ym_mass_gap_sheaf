/-
Endpoint instantiation of the lower-six suffix shape certificate.

The first suffix mode is `thetaWindowRight k + 1`.  Splitting the integer
square-root center modulo four proves the two exact shape inequalities needed
by the rational certificate.  No estimate of an irrational square root is
introduced.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotoneRational
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

local infix:50 " ≈ " => Q'.eqv

private theorem linear_square (a b q : Nat) :
    (a * q + b) * (a * q + b) =
      (a * a) * (q * q) + (a * b) * q + (a * b) * q + b * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
  ac_rfl

private theorem div_four_decomp (c : Nat) :
    c = 4 * (c / 4) + c % 4 := by omega

private theorem mod_four_cases (c : Nat) :
    c % 4 = 0 ∨ c % 4 = 1 ∨ c % 4 = 2 ∨ c % 4 = 3 := by omega

private theorem three_mul_le_square {q : Nat} (hq : 3 ≤ q) :
    3 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem two_mul_le_square {q : Nat} (hq : 2 ≤ q) :
    2 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem nine_mul_le_square {q : Nat} (hq : 9 ≤ q) :
    9 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem center_right_after_endpoint_shape
    {D c : Nat}
    (hc10 : 10 ≤ c)
    (hsq : c * c ≤ 2 * D + 1)
    (hsqNext : 2 * D + 1 < (c + 1) * (c + 1)) :
    let n := c + c / 4 + 2
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let q := c / 4
  have hcdiv : c = 4 * q + c % 4 := by
    simpa [q] using div_four_decomp c
  have hcases := mod_four_cases c
  rcases hcases with h0 | h1 | h2 | h3
  · have hc : c = 4 * q := by omega
    have hq : 3 ≤ q := by omega
    have hqq : 3 * q ≤ q * q := three_mul_le_square hq
    have hdiv : c / 4 = q := by dsimp only [q]
    have hcsq : c * c =
        16 * (q * q) := by
      rw [hc]
      simpa using linear_square 4 0 q
    have hcnextsq : (c + 1) * (c + 1) =
        16 * (q * q) + 4 * q + 4 * q + 1 := by
      rw [hc]
      simpa [Nat.add_assoc] using linear_square 4 1 q
    have hn : c + c / 4 + 2 = 5 * q + 2 := by omega
    have hnsq : (c + c / 4 + 2) * (c + c / 4 + 2) =
        25 * (q * q) + 10 * q + 10 * q + 4 := by
      rw [hn]
      simpa using linear_square 5 2 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega

  · have hc : c = 4 * q + 1 := by omega
    have hq : 3 ≤ q := by omega
    have hqq : 3 * q ≤ q * q := three_mul_le_square hq
    have hdiv : c / 4 = q := by dsimp only [q]
    have hcsq : c * c =
        16 * (q * q) + 4 * q + 4 * q + 1 := by
      rw [hc]
      simpa using linear_square 4 1 q
    have hcnextsq : (c + 1) * (c + 1) =
        16 * (q * q) + 8 * q + 8 * q + 4 := by
      rw [hc]
      have hform : 4 * q + 1 + 1 = 4 * q + 2 := by omega
      rw [hform]
      simpa using linear_square 4 2 q
    have hn : c + c / 4 + 2 = 5 * q + 3 := by omega
    have hnsq : (c + c / 4 + 2) * (c + c / 4 + 2) =
        25 * (q * q) + 15 * q + 15 * q + 9 := by
      rw [hn]
      simpa using linear_square 5 3 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega
  · have hc : c = 4 * q + 2 := by omega
    have hq : 2 ≤ q := by omega
    have hqq : 2 * q ≤ q * q := two_mul_le_square hq
    have hdiv : c / 4 = q := by dsimp only [q]
    have hcsq : c * c =
        16 * (q * q) + 8 * q + 8 * q + 4 := by
      rw [hc]
      simpa using linear_square 4 2 q
    have hcnextsq : (c + 1) * (c + 1) =
        16 * (q * q) + 12 * q + 12 * q + 9 := by
      rw [hc]
      have hform : 4 * q + 2 + 1 = 4 * q + 3 := by omega
      rw [hform]
      simpa using linear_square 4 3 q
    have hn : c + c / 4 + 2 = 5 * q + 4 := by omega
    have hnsq : (c + c / 4 + 2) * (c + c / 4 + 2) =
        25 * (q * q) + 20 * q + 20 * q + 16 := by
      rw [hn]
      simpa using linear_square 5 4 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega
  · have hc : c = 4 * q + 3 := by omega
    have hq : 2 ≤ q := by omega
    have hqq : 2 * q ≤ q * q := two_mul_le_square hq
    have hdiv : c / 4 = q := by dsimp only [q]
    have hcsq : c * c =
        16 * (q * q) + 12 * q + 12 * q + 9 := by
      rw [hc]
      simpa using linear_square 4 3 q
    have hcnextsq : (c + 1) * (c + 1) =
        16 * (q * q) + 16 * q + 16 * q + 16 := by
      rw [hc]
      have hform : 4 * q + 3 + 1 = 4 * q + 4 := by omega
      rw [hform]
      simpa using linear_square 4 4 q
    have hn : c + c / 4 + 2 = 5 * q + 5 := by omega
    have hnsq : (c + c / 4 + 2) * (c + c / 4 + 2) =
        25 * (q * q) + 25 * q + 25 * q + 25 := by
      rw [hn]
      simpa using linear_square 5 5 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega

theorem lowerSixSuffixAfterEndpoint_shape_nat {k : Nat} (hk : 48 ≤ k) :
    let D := k + 2
    let n := thetaWindowRight k + 2
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let c := thetaWindowCenter k
  have hc10 : 10 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hsq : c * c ≤ 2 * (k + 2) + 1 := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hsqNext : 2 * (k + 2) + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * (k + 2) + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  simpa [thetaWindowRight, c] using
    (center_right_after_endpoint_shape hc10 hsq hsqNext)

theorem ofNat_square_eqv (n : Nat) :
    RingNormaliser.qpow (Q'.ofNat n) 2 ≈ Q'.ofNat (n * n) := by
  change (((1 : Q') * Q'.ofNat n) * Q'.ofNat n) ≈ Q'.ofNat (n * n)
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ (Q'.ofNat n)
      (Q'.one_mul_eqv (Q'.ofNat n)))
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv n n))

theorem ofNat_three_mul_eqv (n : Nat) :
    Q'.ofNat 3 * Q'.ofNat n ≈ Q'.ofNat (3 * n) :=
  Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 3 n)

theorem ofNat_shape_left_eqv (n : Nat) :
    Q'.ofNat 5 * (Q'.ofNat 2 * Q'.ofNat n + 1) ≈
      Q'.ofNat (5 * (2 * n + 1)) := by
  have htwo : Q'.ofNat 2 * Q'.ofNat n ≈ Q'.ofNat (2 * n) :=
    Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 2 n)
  have hinner : Q'.ofNat 2 * Q'.ofNat n + 1 ≈
      Q'.ofNat (2 * n + 1) := by
    refine Q'.eqv_trans _
      (Q'.ofNat (2 * n) + Q'.ofNat 1) _ ?_ ?_
    · exact Q'.add_eqv_congr' htwo (by decide)
    · exact Q'.eqv_symm (Q'.ofNat_add_eqv (2 * n) 1)
  exact Q'.eqv_trans _
    (Q'.ofNat 5 * Q'.ofNat (2 * n + 1)) _
    (Q'.mul_eqv_congr_left _ _ _ hinner)
    (Q'.eqv_symm (HeatKernelRGStep.ofNat_mul_eqv 5 (2 * n + 1)))

private theorem ofNat_succ_eqv (n : Nat) :
    Q'.ofNat n + 1 ≈ Q'.ofNat (n + 1) := by
  refine Q'.eqv_trans _ (Q'.ofNat n + Q'.ofNat 1) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _ (by decide)
  · exact Q'.eqv_symm (Q'.ofNat_add_eqv n 1)

private theorem lowerSixAfterEndpoint_shape_q
    {k : Nat} (hk : 48 ≤ k) :
    let D := Q'.ofNat (k + 2)
    let n := thetaWindowRight k + 2
    Q'.ofNat 3 * D ≤ RingNormaliser.qpow (Q'.ofNat n) 2 ∧
      Q'.ofNat 5 * (Q'.ofNat 2 * Q'.ofNat n + 1) ≤
        Q'.ofNat 3 * D := by
  let n := thetaWindowRight k + 2
  have hnat := lowerSixSuffixAfterEndpoint_shape_nat hk
  have hsqNat : Q'.ofNat (3 * (k + 2)) ≤ Q'.ofNat (n * n) :=
    CReal.ofNat_le_ofNat hnat.1
  have hshapeNat : Q'.ofNat (5 * (2 * n + 1)) ≤
      Q'.ofNat (3 * (k + 2)) :=
    CReal.ofNat_le_ofNat hnat.2
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ofNat_three_mul_eqv (k + 2)))
      (Q'.le_trans' _ _ _ hsqNat
        (Q'.le_of_eqv (Q'.eqv_symm (ofNat_square_eqv n))))
  · exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (ofNat_shape_left_eqv n))
      (Q'.le_trans' _ _ _ hshapeNat
        (Q'.le_of_eqv
          (Q'.eqv_symm (ofNat_three_mul_eqv (k + 2)))))

/-- The first mode after the suffix endpoint has nonnegative cleared slack. -/
theorem lowerSixAfterEndpointRawSlack_nonnegative {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (k + 2))
      (Q'.ofNat (thetaWindowRight k + 2)) := by
  have hshape := lowerSixAfterEndpoint_shape_q hk
  exact lowerSixRightRawSlack_nonnegative_of_shape
    (CReal.ofNat_le_ofNat (by omega : 1 ≤ k + 2))
    (HeatKernelRGStep.zero_le_ofNat _)
    hshape.1 hshape.2

private theorem nat_square_mono {a b : Nat} (h : a ≤ b) :
    a * a ≤ b * b := by
  exact Nat.mul_le_mul h h

/-- From the first post-endpoint mode onward, every cleared raw slack is
nonnegative.  This is the uniform suffix induction driven by the exact
forward-difference polynomial. -/
theorem lowerSixSuffixRawSlack_nonnegative_from_second
    {k : Nat} (hk : 48 ≤ k) : ∀ j : Nat,
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (k + 2))
      (Q'.ofNat (thetaWindowRight k + 2 + j))
  | 0 => by
      simpa using lowerSixAfterEndpointRawSlack_nonnegative hk
  | j + 1 => by
      let n0 := thetaWindowRight k + 2
      let n := n0 + j
      have ih := lowerSixSuffixRawSlack_nonnegative_from_second hk j
      have hshape0 := lowerSixSuffixAfterEndpoint_shape_nat hk
      have hn0n : n0 ≤ n := by dsimp only [n, n0]; omega
      have hsqNat : 3 * (k + 2) ≤ n * n :=
        Nat.le_trans hshape0.1 (nat_square_mono hn0n)
      have hsqQ : Q'.ofNat 3 * Q'.ofNat (k + 2) ≤
          RingNormaliser.qpow (Q'.ofNat n) 2 := by
        exact Q'.le_trans' _ _ _
          (Q'.le_of_eqv (ofNat_three_mul_eqv (k + 2)))
          (Q'.le_trans' _ _ _ (CReal.ofNat_le_ofNat hsqNat)
            (Q'.le_of_eqv (Q'.eqv_symm (ofNat_square_eqv n))))
      have hn13 : 13 ≤ n := by
        have hc := thetaWindowCenter_ge_nine (show 38 ≤ k by omega)
        dsimp only [n, n0]
        unfold thetaWindowRight
        omega
      have hmono := lowerSixRightRawSlack_monotone_rational
        (D := Q'.ofNat (k + 2)) (N := Q'.ofNat n)
        (CReal.ofNat_le_ofNat (by omega : 50 ≤ k + 2))
        (CReal.ofNat_le_ofNat hn13) hsqQ
      have hsucc := ofNat_succ_eqv n
      have htransport := lowerSixRightRawSlack_eqv_congr
        (Q'.eqv_refl (Q'.ofNat (k + 2))) hsucc
      have hnext : (0 : Q') ≤ lowerSixRightRawSlack
          (Q'.ofNat (k + 2)) (Q'.ofNat (n + 1)) :=
        Q'.le_trans' _ _ _ ih
          (Q'.le_trans' _ _ _ hmono (Q'.le_of_eqv htransport))
      simpa [n, n0, Nat.add_assoc] using hnext

#print axioms lowerSixSuffixAfterEndpoint_shape_nat
#print axioms lowerSixAfterEndpointRawSlack_nonnegative
#print axioms lowerSixSuffixRawSlack_nonnegative_from_second

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint
