import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftSuffix

namespace ScratchSlopeBudgetAlgebra

set_option maxHeartbeats 500000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftPayment
open YMGap.Continuum.HarmonicWeightDriftFence
open YMGap.Continuum.ReciprocalBernoulliUpper
open YMGap.Continuum.SummableInverseSquare

/-- Fast factorized proof of the natural-number budget used by the
consecutive harmonic-slope estimate. -/
theorem slope_drift_nat_budget_fast
    {D n : Nat} (hD : 1 ≤ D) (hsq : 3 * D ≤ n * n) :
    (n + 1) * (2 * n + 1) * (D + 1) * (D * D - 1) ≤
      (n * n) * (2 * (D * D - 1) + 1) *
        (D + 1 + (2 * n + 1)) := by
  let d := D * D - 1
  let r := n + (2 * n + 1)
  let S := (2 * d) * (2 * n + 1) + (D + 1) + (2 * n + 1)
  have hfirst : r ≤ 3 * (2 * n + 1) := by
    dsimp only [r]
    omega
  have hsecond : D + 1 ≤ 2 * D := by omega
  have hcoeff : r * (D + 1) ≤
      (3 * (2 * n + 1)) * (2 * D) :=
    Nat.mul_le_mul hfirst hsecond
  have hsmall : r * (D + 1) * d ≤
      (3 * (2 * n + 1)) * (2 * D) * d :=
    Nat.mul_le_mul_right d hcoeff
  have hinside : (2 * d) * (2 * n + 1) ≤ S := by
    dsimp only [S]
    omega
  have hshape : 3 * D * S ≤ (n * n) * S :=
    Nat.mul_le_mul_right S hsq
  have hresidual : r * (D + 1) * d ≤
      (n * n) * S := by
    refine Nat.le_trans hsmall ?_
    refine Nat.le_trans ?_ hshape
    refine Nat.le_trans ?_ (Nat.mul_le_mul_left (3 * D) hinside)
    exact Nat.le_of_eq (by ac_rfl)
  have hquad : (n + 1) * (2 * n + 1) =
      2 * (n * n) + r := by
    dsimp only [r]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul]
    ac_rfl
  have hleft :
      (n + 1) * (2 * n + 1) * (D + 1) * d =
        2 * (n * n) * (D + 1) * d +
          r * (D + 1) * d := by
    rw [hquad]
    simp only [Nat.add_mul]
  have hright :
      (n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1)) =
        2 * (n * n) * (D + 1) * d + (n * n) * S := by
    have hinner :
        (2 * d + 1) * (D + 1 + (2 * n + 1)) =
          2 * (D + 1) * d + S := by
      dsimp only [S]
      simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
      ac_rfl
    rw [Nat.mul_assoc, hinner, Nat.mul_add]
    ac_rfl
  change (n + 1) * (2 * n + 1) * (D + 1) * d ≤
    (n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1))
  rw [hleft, hright]
  exact Nat.add_le_add_left hresidual _

#print axioms ScratchSlopeBudgetAlgebra.slope_drift_nat_budget_fast

/-- The same budget in the deliberately unreduced denominator shape emitted
by the raw `Q'` numerator/denominator projection. -/
theorem slope_drift_nat_budget_unreduced
    {D n : Nat} (hD : 1 ≤ D) (hsq : 3 * D ≤ n * n) :
    let d := D * D - 1
    (n + 1) * (2 * n + 1) *
        (d * d * (d * d) * (D + 1)) ≤
      (n * n) * ((d + d) * (d * d) + d * d) *
          (D + 1 + (2 * n + 1)) * d := by
  let d := D * D - 1
  have hnat := slope_drift_nat_budget_fast hD hsq
  have hscaled := Nat.mul_le_mul_right (d * d * d) hnat
  dsimp only
  change
    ((n + 1) * (2 * n + 1) * (D + 1) * d) * (d * d * d) ≤
      ((n * n) * (2 * d + 1) * (D + 1 + (2 * n + 1))) *
        (d * d * d) at hscaled
  have hfactor :
      ((d + d) * (d * d) + d * d) =
        (2 * d + 1) * (d * d) := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
  rw [hfactor]
  calc
    _ = ((n + 1) * (2 * n + 1) * (D + 1) * d) *
          (d * d * d) := by
      dsimp only [d]
      ac_rfl
    _ ≤ ((n * n) * (2 * d + 1) *
          (D + 1 + (2 * n + 1))) * (d * d * d) := hscaled
    _ = _ := by
      dsimp only [d]
      ac_rfl

#print axioms ScratchSlopeBudgetAlgebra.slope_drift_nat_budget_unreduced

theorem slope_drift_q_budget_scout
    {k n : Nat} (hsq : 3 * (k + 2) ≤ n * n) :
    let A := Q'.ofNat (n + 1)
    let P := Q'.ofNat (2 * n + 1)
    let u := unit (driftDen k) (driftDen_pos k)
    let B := bernDen (harmU (k + 1)) (2 * n + 1)
    A * P * u ≤
      (Q'.ofNat (n * n) * lowerSixDriftExcess k) * B := by
  dsimp only
  show
      (Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) *
        unit (driftDen k) (driftDen_pos k)).num *
          (((Q'.ofNat (n * n) * lowerSixDriftExcess k) *
            bernDen (harmU (k + 1)) (2 * n + 1)).den : Int) ≤
        ((Q'.ofNat (n * n) * lowerSixDriftExcess k) *
          bernDen (harmU (k + 1)) (2 * n + 1)).num *
            (Q'.ofNat (n + 1) * Q'.ofNat (2 * n + 1) *
              unit (driftDen k) (driftDen_pos k)).den
  unfold lowerSixDriftExcess driftDen harmU unit bernDen
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.add_num_cast, Q'.add_den_cast,
    Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one, Int.one_mul]
  have h1n : (1 : Q').num = 1 := rfl
  have h1d : ((1 : Q').den : Int) = 1 := rfl
  rw [h1n, h1d, Int.mul_one, Int.one_mul]
  push_cast
  have hnat := slope_drift_nat_budget_unreduced
    (D := k + 2) (n := n) (by omega) hsq
  dsimp only at hnat
  rw [show k + 2 + 1 = k + 1 + 1 + 1 by omega] at hnat
  exact_mod_cast hnat

#print axioms ScratchSlopeBudgetAlgebra.slope_drift_q_budget_scout

end ScratchSlopeBudgetAlgebra
