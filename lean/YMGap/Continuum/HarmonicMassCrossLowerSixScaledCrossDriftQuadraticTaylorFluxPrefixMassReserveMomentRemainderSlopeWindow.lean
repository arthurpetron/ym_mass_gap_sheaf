/-
Uniform cubic root-slope error on the physical theta prefix.

The square-root geometry of the window turns the formal cubic Taylor error
into an absolute `1/40` enclosure throughout the production range.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeEnclosure

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeWindow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeEnclosure
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.SummableInverseSquare

private theorem thetaWindowRight_le_twice_center (k : Nat) :
    thetaWindowRight k ≤ 2 * thetaWindowCenter k := by
  unfold thetaWindowRight
  have h := Nat.div_le_self (thetaWindowCenter k) 4
  omega

/-- On the physical prefix, the exponent `2n+1` has square at most `35D`. -/
private theorem odd_prefix_exponent_sq_le
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowRight k) :
    (2 * n + 1) * (2 * n + 1) ≤ 35 * (k + 2) := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc9 : 9 ≤ c := by
    dsimp only [c]
    exact thetaWindowCenter_ge_nine (by omega)
  have hn2c : n ≤ 2 * c :=
    Nat.le_trans hn (by
      dsimp only [c]
      exact thetaWindowRight_le_twice_center k)
  have hm : 2 * n + 1 ≤ 4 * c + 1 := by omega
  have hmsq : (2 * n + 1) * (2 * n + 1) ≤
      (4 * c + 1) * (4 * c + 1) := Nat.mul_le_mul hm hm
  have h8 : 8 * c < c * c := by
    have h8c : 8 < c := by omega
    exact Nat.mul_lt_mul_of_pos_right h8c (by omega)
  have hpoly : (4 * c + 1) * (4 * c + 1) ≤ 17 * (c * c) := by
    have hexpand : (4 * c + 1) * (4 * c + 1) =
        16 * (c * c) + 8 * c + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      have hfour : (4 * c) * (4 * c) = 16 * (c * c) := by ac_rfl
      rw [hfour]
      omega
    rw [hexpand]
    omega
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hD : 8191 ≤ D := by
    dsimp only [D]
    omega
  exact Nat.le_trans hmsq
    (Nat.le_trans hpoly (by
      have h17 := Nat.mul_le_mul_left 17 hcsq
      omega))

private theorem rootSlope_error_numerator_bound
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowRight k) :
    40 * ((n + 1) * cubicCoeff (2 * n + 1)) ≤
      (k + 2) * (k + 2) * (k + 2) := by
  let m := 2 * n + 1
  let D := k + 2
  let A := (n + 1) * cubicCoeff m
  have hcoeff := six_cubicCoeff_le_cube m
  have hn1m : n + 1 ≤ m := by
    dsimp only [m]
    omega
  have hscaled : (n + 1) * (6 * cubicCoeff m) ≤
      (n + 1) * (m * m * m) :=
    Nat.mul_le_mul_left (n + 1) hcoeff
  have hm4 : (n + 1) * (m * m * m) ≤ (m * m) * (m * m) := by
    have h := Nat.mul_le_mul_right (m * m * m) hn1m
    calc
      (n + 1) * (m * m * m) ≤ m * (m * m * m) := h
      _ = (m * m) * (m * m) := by ac_rfl
  have hm2 : m * m ≤ 35 * D := by
    dsimp only [m, D]
    exact odd_prefix_exponent_sq_le hk hn
  have hm4bound : (m * m) * (m * m) ≤
      (35 * D) * (35 * D) := Nat.mul_le_mul hm2 hm2
  have h6A : 6 * A ≤ 1225 * (D * D) := by
    calc
      6 * A = (n + 1) * (6 * cubicCoeff m) := by
        dsimp only [A]
        ac_rfl
      _ ≤ (n + 1) * (m * m * m) := hscaled
      _ ≤ (m * m) * (m * m) := hm4
      _ ≤ (35 * D) * (35 * D) := hm4bound
      _ = (35 * 35) * (D * D) := by ac_rfl
      _ = 1225 * (D * D) := by
        rw [show 35 * 35 = 1225 by decide]
  have hD : 8191 ≤ D := by
    dsimp only [D]
    omega
  have h49000 : 6 * (40 * A) ≤ 49000 * (D * D) := by
    have h40 := Nat.mul_le_mul_left 40 h6A
    calc
      6 * (40 * A) = 40 * (6 * A) := by ac_rfl
      _ ≤ 40 * (1225 * (D * D)) := h40
      _ = (40 * 1225) * (D * D) := by ac_rfl
      _ = 49000 * (D * D) := by
        rw [show 40 * 1225 = 49000 by decide]
  have hcoef : 49000 ≤ 6 * D := by omega
  have h6cube : 49000 * (D * D) ≤ 6 * (D * D * D) := by
    calc
      49000 * (D * D) ≤ (6 * D) * (D * D) :=
        Nat.mul_le_mul_right (D * D) hcoef
      _ = 6 * (D * D * D) := by ac_rfl
  have hcancel : 6 * (40 * A) ≤ 6 * (D * D * D) :=
    Nat.le_trans h49000 h6cube
  have hresult : 40 * A ≤ D * D * D :=
    Nat.le_of_mul_le_mul_left hcancel (by omega)
  simpa only [A, m, D] using hresult

/-- Uniform `1/40` cubic error for every adjacent-root slope in the theta
prefix at the production threshold. -/
theorem lowerSixRootSlopeTaylor2Error_le_oneFortieth_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowRight k) :
    rootSlopeTaylor2Error (harmU k) n ≤
      Q'.mkPos 1 40 (by decide) := by
  have hnat := rootSlope_error_numerator_bound hk hn
  unfold rootSlopeTaylor2Error harmU unit
  show
    (Q'.ofNat (n + 1) *
      (Q'.ofNat (cubicCoeff (2 * n + 1)) *
        (Q'.mkPos 1 (k + 2) (by omega) *
          (Q'.mkPos 1 (k + 2) (by omega) *
            Q'.mkPos 1 (k + 2) (by omega))))).num *
        ((Q'.mkPos 1 40 (by decide)).den : Int) ≤
      (Q'.mkPos 1 40 (by decide)).num *
        (Q'.ofNat (n + 1) *
          (Q'.ofNat (cubicCoeff (2 * n + 1)) *
            (Q'.mkPos 1 (k + 2) (by omega) *
              (Q'.mkPos 1 (k + 2) (by omega) *
                Q'.mkPos 1 (k + 2) (by omega))))).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  push_cast
  have hnat' :
      ((n + 1) * cubicCoeff (2 * n + 1)) * 40 ≤
        (k + 2) * ((k + 2) * (k + 2)) := by
    calc
      ((n + 1) * cubicCoeff (2 * n + 1)) * 40 =
          40 * ((n + 1) * cubicCoeff (2 * n + 1)) := by ac_rfl
      _ ≤ (k + 2) * (k + 2) * (k + 2) := hnat
      _ = (k + 2) * ((k + 2) * (k + 2)) := by ac_rfl
  exact_mod_cast hnat'

#print axioms lowerSixRootSlopeTaylor2Error_le_oneFortieth_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeWindow
