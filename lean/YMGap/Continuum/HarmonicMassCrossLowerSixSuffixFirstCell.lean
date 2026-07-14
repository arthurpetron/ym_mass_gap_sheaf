/-
The nominal first cell of the lower-six right suffix.

The post-endpoint monotonicity layer starts one mode later because the floor
in `thetaWindowRight` can make `N^2 < 3D` at the first cell.  For centers at
least 36 the original shape certificate is again valid.  The remaining exact
finite prefix is isolated below as a kernel-decided rational bootstrap.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixFirstCell

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixEndpoint
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

private theorem nine_mul_le_square {q : Nat} (hq : 9 ≤ q) :
    9 * q ≤ q * q := by
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hq

private theorem center_right_endpoint_shape_large
    {D c : Nat}
    (hc36 : 36 ≤ c)
    (hsq : c * c ≤ 2 * D + 1)
    (hsqNext : 2 * D + 1 < (c + 1) * (c + 1)) :
    let n := c + c / 4 + 1
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let q := c / 4
  have hcdiv : c = 4 * q + c % 4 := by
    simpa [q] using div_four_decomp c
  have hcases := mod_four_cases c
  rcases hcases with h0 | h1 | h2 | h3
  · have hc : c = 4 * q := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
    have hdiv : c / 4 = q := by dsimp only [q]
    have hcsq : c * c = 16 * (q * q) := by
      rw [hc]
      simpa using linear_square 4 0 q
    have hcnextsq : (c + 1) * (c + 1) =
        16 * (q * q) + 4 * q + 4 * q + 1 := by
      rw [hc]
      simpa [Nat.add_assoc] using linear_square 4 1 q
    have hn : c + c / 4 + 1 = 5 * q + 1 := by omega
    have hnsq : (c + c / 4 + 1) * (c + c / 4 + 1) =
        25 * (q * q) + 5 * q + 5 * q + 1 := by
      rw [hn]
      simpa using linear_square 5 1 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega
  · have hc : c = 4 * q + 1 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
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
    have hn : c + c / 4 + 1 = 5 * q + 2 := by omega
    have hnsq : (c + c / 4 + 1) * (c + c / 4 + 1) =
        25 * (q * q) + 10 * q + 10 * q + 4 := by
      rw [hn]
      simpa using linear_square 5 2 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega
  · have hc : c = 4 * q + 2 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
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
    have hn : c + c / 4 + 1 = 5 * q + 3 := by omega
    have hnsq : (c + c / 4 + 1) * (c + c / 4 + 1) =
        25 * (q * q) + 15 * q + 15 * q + 9 := by
      rw [hn]
      simpa using linear_square 5 3 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega
  · have hc : c = 4 * q + 3 := by omega
    have hq : 9 ≤ q := by omega
    have hqq : 9 * q ≤ q * q := nine_mul_le_square hq
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
    have hn : c + c / 4 + 1 = 5 * q + 4 := by omega
    have hnsq : (c + c / 4 + 1) * (c + c / 4 + 1) =
        25 * (q * q) + 20 * q + 20 * q + 16 := by
      rw [hn]
      simpa using linear_square 5 4 q
    dsimp only
    rw [hcsq] at hsq
    rw [hcnextsq] at hsqNext
    rw [hnsq]
    rw [hn]
    constructor <;> omega

theorem lowerSixSuffixEndpoint_shape_nat_large {k : Nat} (hk : 646 ≤ k) :
    let D := k + 2
    let n := thetaWindowRight k + 1
    3 * D ≤ n * n ∧ 5 * (2 * n + 1) ≤ 3 * D := by
  let c := thetaWindowCenter k
  have hc36 : 36 ≤ c := by
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
    (center_right_endpoint_shape_large hc36 hsq hsqNext)

private theorem lowerSixEndpoint_shape_q_large
    {k : Nat} (hk : 646 ≤ k) :
    let D := Q'.ofNat (k + 2)
    let n := thetaWindowRight k + 1
    Q'.ofNat 3 * D ≤ RingNormaliser.qpow (Q'.ofNat n) 2 ∧
      Q'.ofNat 5 * (Q'.ofNat 2 * Q'.ofNat n + 1) ≤
        Q'.ofNat 3 * D := by
  let n := thetaWindowRight k + 1
  have hnat := lowerSixSuffixEndpoint_shape_nat_large hk
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

theorem lowerSixEndpointRawSlack_nonnegative_large
    {k : Nat} (hk : 646 ≤ k) :
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (k + 2))
      (Q'.ofNat (thetaWindowRight k + 1)) := by
  have hshape := lowerSixEndpoint_shape_q_large hk
  exact lowerSixRightRawSlack_nonnegative_of_shape
    (CReal.ofNat_le_ofNat (by omega : 1 ≤ k + 2))
    (HeatKernelRGStep.zero_le_ofNat _)
    hshape.1 hshape.2

/-- Exact kernel bootstrap for the finite floor-effect band below the stable
center threshold.  Every quantity is a derived closed rational. -/
theorem lowerSixEndpointRawSlack_nonnegative_small : ∀ i : Fin 598,
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (i.val + 50))
      (Q'.ofNat (thetaWindowRight (i.val + 48) + 1)) := by
  decide

theorem lowerSixEndpointRawSlack_nonnegative
    {k : Nat} (hk : 48 ≤ k) :
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (k + 2))
      (Q'.ofNat (thetaWindowRight k + 1)) := by
  by_cases hlarge : 646 ≤ k
  · exact lowerSixEndpointRawSlack_nonnegative_large hlarge
  · let i : Fin 598 := ⟨k - 48, by omega⟩
    have h := lowerSixEndpointRawSlack_nonnegative_small i
    have hkidx : k - 48 + 48 = k := by omega
    have hD : k - 48 + 50 = k + 2 := by omega
    simpa [i, hkidx, hD] using h

/-- Every cleared raw slack on the full nominal right suffix is nonnegative. -/
theorem lowerSixSuffixRawSlack_nonnegative
    {k : Nat} (hk : 48 ≤ k) : ∀ j : Nat,
    (0 : Q') ≤ lowerSixRightRawSlack (Q'.ofNat (k + 2))
      (Q'.ofNat (thetaWindowRight k + 1 + j))
  | 0 => by simpa using lowerSixEndpointRawSlack_nonnegative hk
  | j + 1 => by
      have h := lowerSixSuffixRawSlack_nonnegative_from_second hk j
      have hidx : thetaWindowRight k + 2 + j =
          thetaWindowRight k + 1 + (j + 1) := by omega
      rw [← hidx]
      exact h

#print axioms lowerSixSuffixEndpoint_shape_nat_large
#print axioms lowerSixEndpointRawSlack_nonnegative_large
#print axioms lowerSixEndpointRawSlack_nonnegative_small
#print axioms lowerSixEndpointRawSlack_nonnegative
#print axioms lowerSixSuffixRawSlack_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixFirstCell
