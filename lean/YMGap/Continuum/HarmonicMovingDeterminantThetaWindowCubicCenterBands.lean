/-
Constructive parity decomposition of the moving integer-square-root center.
The remainder bounds are exactly those consumed by the even/odd endpoint
certificates.
-/

import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpointPhysical

namespace YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands

set_option maxHeartbeats 2400000
set_option maxRecDepth 30000

open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow

private theorem even_square (m : Nat) :
    (2 * m) * (2 * m) = 2 * (2 * m * m) := by ac_rfl

private theorem even_succ_square (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      2 * (2 * m * m + 2 * m) + 1 := by
  rw [Nat.add_mul, Nat.mul_add, even_square]
  omega

private theorem two_m_mul_succ (m : Nat) :
    2 * m * (m + 1) = 2 * m * m + 2 * m := by
  rw [Nat.mul_add]
  omega

private theorem odd_square (m : Nat) :
    (2 * m + 1) * (2 * m + 1) =
      2 * (2 * m * (m + 1)) + 1 := by
  rw [Nat.add_mul, Nat.mul_add, even_square]
  rw [two_m_mul_succ]
  omega

private theorem odd_succ_square (m : Nat) :
    (2 * m + 1 + 1) * (2 * m + 1 + 1) =
      2 * (2 * m * (m + 1) + 2 * m + 1) + 2 := by
  have hform : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
  rw [hform, even_square]
  have hexpand : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [hexpand, Nat.add_mul]
  omega

/-- Exact center-band data from the floor-square-root inequalities. -/
theorem thetaWindowCenter_band_data {k : Nat} (hk : 48 ≤ k) :
    (∃ M r : Nat,
      thetaWindowCenter k = 2 * (M + 5) ∧
      k + 2 = 2 * (M + 5) * (M + 5) + r ∧
      r ≤ 2 * M + 9) ∨
    (∃ M r : Nat,
      thetaWindowCenter k = 2 * (M + 5) + 1 ∧
      k + 2 = 2 * (M + 5) * (M + 6) + r ∧
      r ≤ 2 * M + 11) := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc10 : 10 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hsqNext : 2 * D + 1 < (c + 1) * (c + 1) := by
    rcases Nat.lt_or_ge (2 * D + 1) ((c + 1) * (c + 1)) with h | h
    · exact h
    · have hbad : c + 1 ≤ c := by
        dsimp only [c, D, thetaWindowCenter, thetaWindowLength] at h ⊢
        exact ChebOrthoMidpointEst.isqrt_ge h
      omega
  have hpar : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hpar with heven | hodd
  · let m := c / 2
    have hc : c = 2 * m := by dsimp only [m]; omega
    have hm : 5 ≤ m := by omega
    let M := m - 5
    have hmM : m = M + 5 := by dsimp only [M]; omega
    have hbase : 2 * m * m ≤ D := by
      rw [hc] at hsq
      rw [even_square] at hsq
      omega
    let r := D - 2 * m * m
    have hD : D = 2 * m * m + r := by dsimp only [r]; omega
    have hr : r ≤ 2 * M + 9 := by
      rw [hc] at hsqNext
      rw [even_succ_square] at hsqNext
      have hrm : r ≤ 2 * m - 1 := by
        dsimp only [r]
        omega
      rw [hmM] at hrm
      dsimp only [M]
      omega
    left
    refine ⟨M, r, ?_, ?_, hr⟩
    · simpa [hmM] using hc
    · simpa [hmM] using hD
  · let m := c / 2
    have hc : c = 2 * m + 1 := by dsimp only [m]; omega
    have hm : 5 ≤ m := by omega
    let M := m - 5
    have hmM : m = M + 5 := by dsimp only [M]; omega
    have hbase : 2 * m * (m + 1) ≤ D := by
      rw [hc] at hsq
      rw [odd_square] at hsq
      omega
    let r := D - 2 * m * (m + 1)
    have hD : D = 2 * m * (m + 1) + r := by dsimp only [r]; omega
    have hr : r ≤ 2 * M + 11 := by
      rw [hc] at hsqNext
      rw [odd_succ_square] at hsqNext
      have hrm : r ≤ 2 * m + 1 := by
        dsimp only [r]
        omega
      rw [hmM] at hrm
      dsimp only [M]
      omega
    right
    refine ⟨M, r, ?_, ?_, hr⟩
    · simpa [hmM] using hc
    · have hm6 : m + 1 = M + 6 := by omega
      simpa [hmM, hm6] using hD

#print axioms thetaWindowCenter_band_data

end YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicCenterBands
