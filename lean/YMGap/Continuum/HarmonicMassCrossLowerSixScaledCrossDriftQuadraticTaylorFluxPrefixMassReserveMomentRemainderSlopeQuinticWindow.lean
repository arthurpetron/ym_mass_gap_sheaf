/-
Sharp quintic root-slope error on the physical theta prefix.

The fourth-order adjacent-root slope enclosure has a fifth-order error.  On
the left square-root window, its Pascal numerator is at most `D^3`, while its
denominator is `D^5`.  This retains the exact `D^-2` scale needed after the
finite-Hermite `D^4` clearing.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuintic

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuinticWindow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuintic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- Exact division-free closed form for the fourth Pascal coefficient. -/
theorem quarticCoeff_twentyFour (m : Nat) :
    24 * quarticCoeff m =
      m * (m - 1) * (m - 2) * (m - 3) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [quarticCoeff]
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => rfl
          | succ m =>
              cases m with
              | zero => rfl
              | succ n =>
                  have ih' : 24 * quarticCoeff (n + 3) =
                      (n + 3) * (n + 2) * (n + 1) * n := by
                    simpa only [Nat.add_sub_cancel] using ih
                  have hc : 6 * cubicCoeff (n + 3) =
                      (n + 3) * (n + 2) * (n + 1) := by
                    simpa only [Nat.add_sub_cancel] using
                      cubicCoeff_six (n + 3)
                  simp only [Nat.add_sub_cancel] at ⊢
                  calc
                    24 * (quarticCoeff (n + 3) + cubicCoeff (n + 3)) =
                        24 * quarticCoeff (n + 3) +
                          24 * cubicCoeff (n + 3) :=
                      Nat.mul_add _ _ _
                    _ = ((n + 3) * (n + 2) * (n + 1)) * n +
                        4 * (6 * cubicCoeff (n + 3)) := by
                      rw [ih']
                      ac_rfl
                    _ = ((n + 3) * (n + 2) * (n + 1)) * n +
                        4 * ((n + 3) * (n + 2) * (n + 1)) := by rw [hc]
                    _ = ((n + 3) * (n + 2) * (n + 1)) * n +
                        ((n + 3) * (n + 2) * (n + 1)) * 4 := by ac_rfl
                    _ = ((n + 3) * (n + 2) * (n + 1)) * (n + 4) :=
                      (Nat.mul_add _ _ _).symm
                    _ = (n + 4) * (n + 3) * (n + 2) * (n + 1) := by
                      ac_rfl

/-- Factorial-scaled fourth Pascal coefficient bound. -/
theorem twentyFour_quarticCoeff_le_fourth (m : Nat) :
    24 * quarticCoeff m ≤ (m * m) * (m * m) := by
  rw [quarticCoeff_twentyFour]
  calc
    m * (m - 1) * (m - 2) * (m - 3) ≤
        m * m * m * m :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.le_refl m) (Nat.sub_le m 1))
          (Nat.sub_le m 2))
        (Nat.sub_le m 3)
    _ = (m * m) * (m * m) := by ac_rfl

/-- Exact division-free closed form for the fifth Pascal coefficient. -/
theorem quinticCoeff_oneTwenty (m : Nat) :
    120 * quinticCoeff m =
      m * (m - 1) * (m - 2) * (m - 3) * (m - 4) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [quinticCoeff]
      cases m with
      | zero => rfl
      | succ m =>
          cases m with
          | zero => rfl
          | succ m =>
              cases m with
              | zero => rfl
              | succ m =>
                  cases m with
                  | zero => rfl
                  | succ n =>
                      have ih' : 120 * quinticCoeff (n + 4) =
                          (n + 4) * (n + 3) * (n + 2) * (n + 1) * n := by
                        simpa only [Nat.add_sub_cancel] using ih
                      have hq : 24 * quarticCoeff (n + 4) =
                          (n + 4) * (n + 3) * (n + 2) * (n + 1) := by
                        simpa only [Nat.add_sub_cancel] using
                          quarticCoeff_twentyFour (n + 4)
                      simp only [Nat.add_sub_cancel] at ⊢
                      calc
                        120 * (quinticCoeff (n + 4) + quarticCoeff (n + 4)) =
                            120 * quinticCoeff (n + 4) +
                              120 * quarticCoeff (n + 4) :=
                          Nat.mul_add _ _ _
                        _ = ((n + 4) * (n + 3) * (n + 2) * (n + 1)) * n +
                            5 * (24 * quarticCoeff (n + 4)) := by
                          rw [ih']
                          ac_rfl
                        _ = ((n + 4) * (n + 3) * (n + 2) * (n + 1)) * n +
                            5 * ((n + 4) * (n + 3) * (n + 2) * (n + 1)) := by
                          rw [hq]
                        _ = ((n + 4) * (n + 3) * (n + 2) * (n + 1)) * n +
                            ((n + 4) * (n + 3) * (n + 2) * (n + 1)) * 5 := by
                          ac_rfl
                        _ = ((n + 4) * (n + 3) * (n + 2) * (n + 1)) *
                            (n + 5) := (Nat.mul_add _ _ _).symm
                        _ = (n + 5) * (n + 4) * (n + 3) * (n + 2) *
                            (n + 1) := by ac_rfl

/-- Factorial-scaled fifth Pascal coefficient bound. -/
theorem oneTwenty_quinticCoeff_le_fifth (m : Nat) :
    120 * quinticCoeff m ≤ m * ((m * m) * (m * m)) := by
  rw [quinticCoeff_oneTwenty]
  calc
    m * (m - 1) * (m - 2) * (m - 3) * (m - 4) ≤
        m * m * m * m * m :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.le_refl m) (Nat.sub_le m 1))
            (Nat.sub_le m 2))
          (Nat.sub_le m 3))
        (Nat.sub_le m 4)
    _ = m * ((m * m) * (m * m)) := by ac_rfl

private theorem ten_center_le_harmonicDen
    {k : Nat} (hk : 247 ≤ k) :
    10 * thetaWindowCenter k ≤ k + 2 := by
  let c := thetaWindowCenter k
  let D := k + 2
  have hc22 : 22 ≤ c := by
    dsimp only [c, thetaWindowCenter, thetaWindowLength]
    apply ChebOrthoMidpointEst.isqrt_ge
    omega
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have h20c : 20 * c ≤ c * c := by
    have h := Nat.mul_le_mul_right c (show 20 ≤ c by omega)
    simpa [Nat.mul_comm] using h
  rcases Nat.le_total (10 * c) D with h | h
  · change 10 * c ≤ D
    exact h
  · rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hupper : 2 * D + 1 < 20 * c := by omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · change 10 * c ≤ D
      omega

/-- On the left square-root prefix, the odd exponent has square at most three
times the harmonic denominator. -/
private theorem odd_left_exponent_sq_le_den
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (2 * n + 1) * (2 * n + 1) ≤ 3 * (k + 2) := by
  let c := thetaWindowCenter k
  let D := k + 2
  let m := 2 * n + 1
  have hc10 : 10 * c ≤ D := by
    dsimp only [c, D]
    exact ten_center_le_harmonicDen (by omega)
  have h2n : 2 * n ≤ c := by
    dsimp only [c]
    unfold thetaWindowLeft at hn
    omega
  have hm : m ≤ c + 1 := by
    dsimp only [m]
    omega
  have hsquare : m * m ≤ (c + 1) * (c + 1) :=
    Nat.mul_le_mul hm hm
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hD : 8191 ≤ D := by
    dsimp only [D]
    omega
  have hright : (c + 1) * (c + 1) ≤ 3 * D := by
    have hexpand : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    rw [hexpand]
    omega
  simpa only [m, D] using Nat.le_trans hsquare hright

private theorem rootSlopeTaylor4_error_numerator_bound
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (n + 1) * quinticCoeff (2 * n + 1) ≤
      (k + 2) * ((k + 2) * (k + 2)) := by
  let m := 2 * n + 1
  let D := k + 2
  have hcoeff := oneTwenty_quinticCoeff_le_fifth m
  have hn1m : n + 1 ≤ m := by
    dsimp only [m]
    omega
  have hm2 : m * m ≤ 3 * D := by
    dsimp only [m, D]
    exact odd_left_exponent_sq_le_den hk hn
  have hleft : 120 * ((n + 1) * quinticCoeff m) ≤
      (m * m) * ((m * m) * (m * m)) := by
    calc
      120 * ((n + 1) * quinticCoeff m) =
          (n + 1) * (120 * quinticCoeff m) := by ac_rfl
      _ ≤ (n + 1) * (m * ((m * m) * (m * m))) :=
        Nat.mul_le_mul_left (n + 1) hcoeff
      _ ≤ m * (m * ((m * m) * (m * m))) :=
        Nat.mul_le_mul_right (m * ((m * m) * (m * m))) hn1m
      _ = (m * m) * ((m * m) * (m * m)) := by ac_rfl
  have hcube : (m * m) * ((m * m) * (m * m)) ≤
      27 * (D * (D * D)) := by
    calc
      (m * m) * ((m * m) * (m * m)) ≤
          (3 * D) * ((3 * D) * (3 * D)) :=
        Nat.mul_le_mul hm2 (Nat.mul_le_mul hm2 hm2)
      _ = 27 * (D * (D * D)) := by ac_rfl
  have h120 : 120 * ((n + 1) * quinticCoeff m) ≤
      120 * (D * (D * D)) := by
    exact Nat.le_trans (Nat.le_trans hleft hcube)
      (Nat.mul_le_mul_right (D * (D * D)) (by decide : 27 ≤ 120))
  have hcancel : (n + 1) * quinticCoeff m ≤ D * (D * D) :=
    Nat.le_of_mul_le_mul_left h120 (by decide)
  simpa only [m, D] using hcancel

/-- On the physical left prefix, the exact fifth-order root-slope error is
at most `1/(k+2)^2`. -/
theorem lowerSixRootSlopeTaylor4Error_le_invDenSq_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    rootSlopeTaylor4Error (harmU k) n ≤
      Q'.mkPos 1 ((k + 2) * (k + 2))
        (Nat.mul_pos (by omega) (by omega)) := by
  have hnat := rootSlopeTaylor4_error_numerator_bound hk hn
  unfold rootSlopeTaylor4Error harmU unit
  show
    (Q'.ofNat (n + 1) *
      (Q'.ofNat (quinticCoeff (2 * n + 1)) *
        (Q'.mkPos 1 (k + 2) (by omega) *
          (Q'.mkPos 1 (k + 2) (by omega) *
            (Q'.mkPos 1 (k + 2) (by omega) *
              (Q'.mkPos 1 (k + 2) (by omega) *
                Q'.mkPos 1 (k + 2) (by omega))))))).num *
        ((Q'.mkPos 1 ((k + 2) * (k + 2))
          (Nat.mul_pos (by omega) (by omega))).den : Int) ≤
      (Q'.mkPos 1 ((k + 2) * (k + 2))
        (Nat.mul_pos (by omega) (by omega))).num *
        (Q'.ofNat (n + 1) *
          (Q'.ofNat (quinticCoeff (2 * n + 1)) *
            (Q'.mkPos 1 (k + 2) (by omega) *
              (Q'.mkPos 1 (k + 2) (by omega) *
                (Q'.mkPos 1 (k + 2) (by omega) *
                  (Q'.mkPos 1 (k + 2) (by omega) *
                    Q'.mkPos 1 (k + 2) (by omega))))))).den
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  push_cast
  have hnat' :
      ((n + 1) * quinticCoeff (2 * n + 1)) *
          ((k + 2) * (k + 2)) ≤
        (k + 2) * ((k + 2) *
          ((k + 2) * ((k + 2) * (k + 2)))) := by
    have hscaled := Nat.mul_le_mul_right ((k + 2) * (k + 2)) hnat
    calc
      ((n + 1) * quinticCoeff (2 * n + 1)) *
          ((k + 2) * (k + 2)) ≤
        ((k + 2) * ((k + 2) * (k + 2))) *
          ((k + 2) * (k + 2)) := hscaled
      _ = (k + 2) * ((k + 2) *
          ((k + 2) * ((k + 2) * (k + 2)))) := by ac_rfl
  exact_mod_cast hnat'

/-- Production-window upper enclosure with the symbolic fifth-order error
replaced by the sharp harmonic inverse-square budget. -/
theorem lowerSixThetaRootSlope_le_Taylor4_add_invDenSq_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    thetaRootSlope k n ≤
      rootSlopeTaylor4 (harmU k) n +
        Q'.mkPos 1 ((k + 2) * (k + 2))
          (Nat.mul_pos (by omega) (by omega)) := by
  exact Q'.le_trans' _ _ _
    (lowerSixThetaRootSlope_le_Taylor4_add_error k n)
    (Q'.add_le_add_left _ _ _
      (lowerSixRootSlopeTaylor4Error_le_invDenSq_large hk hn))

#print axioms twentyFour_quarticCoeff_le_fourth
#print axioms oneTwenty_quinticCoeff_le_fifth
#print axioms lowerSixRootSlopeTaylor4Error_le_invDenSq_large
#print axioms lowerSixThetaRootSlope_le_Taylor4_add_invDenSq_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuinticWindow
