/-
Sharp seventh-order root-slope error on the physical theta prefix.

The exact factorial scaling `5040 * C(m,7) <= m^7`, combined with the
square-root bound `(2n+1)^2 <= 3D`, turns the formal seventh-order error into
the harmonic width `D^-3` needed by the coupled old/next carrier squares.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuinticWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuinticWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

/-- Exact division-free closed form for the sixth Pascal coefficient. -/
theorem sexticCoeff_sevenTwenty (m : Nat) :
    720 * sexticCoeff m =
      m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [sexticCoeff]
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
                  | succ m =>
                      cases m with
                      | zero => rfl
                      | succ n =>
                          have ih' : 720 * sexticCoeff (n + 5) =
                              (n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                (n + 1) * n := by
                            simpa only [Nat.add_sub_cancel] using ih
                          have hq : 120 * quinticCoeff (n + 5) =
                              (n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                (n + 1) := by
                            simpa only [Nat.add_sub_cancel] using
                              quinticCoeff_oneTwenty (n + 5)
                          simp only [Nat.add_sub_cancel] at ⊢
                          calc
                            720 * (sexticCoeff (n + 5) +
                                quinticCoeff (n + 5)) =
                              720 * sexticCoeff (n + 5) +
                                720 * quinticCoeff (n + 5) :=
                                  Nat.mul_add _ _ _
                            _ = ((n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                  (n + 1)) * n +
                                6 * (120 * quinticCoeff (n + 5)) := by
                              rw [ih']
                              ac_rfl
                            _ = ((n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                  (n + 1)) * n +
                                6 * ((n + 5) * (n + 4) * (n + 3) *
                                  (n + 2) * (n + 1)) := by rw [hq]
                            _ = ((n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                  (n + 1)) * n +
                                ((n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                  (n + 1)) * 6 := by ac_rfl
                            _ = ((n + 5) * (n + 4) * (n + 3) * (n + 2) *
                                  (n + 1)) * (n + 6) :=
                              (Nat.mul_add _ _ _).symm
                            _ = (n + 6) * (n + 5) * (n + 4) * (n + 3) *
                                (n + 2) * (n + 1) := by ac_rfl

/-- Exact division-free closed form for the seventh Pascal coefficient. -/
theorem septicCoeff_fiveThousandForty (m : Nat) :
    5040 * septicCoeff m =
      m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) *
        (m - 6) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [septicCoeff]
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
                  | succ m =>
                      cases m with
                      | zero => rfl
                      | succ m =>
                          cases m with
                          | zero => rfl
                          | succ n =>
                              have ih' : 5040 * septicCoeff (n + 6) =
                                  (n + 6) * (n + 5) * (n + 4) * (n + 3) *
                                    (n + 2) * (n + 1) * n := by
                                simpa only [Nat.add_sub_cancel] using ih
                              have hs : 720 * sexticCoeff (n + 6) =
                                  (n + 6) * (n + 5) * (n + 4) * (n + 3) *
                                    (n + 2) * (n + 1) := by
                                simpa only [Nat.add_sub_cancel] using
                                  sexticCoeff_sevenTwenty (n + 6)
                              simp only [Nat.add_sub_cancel] at ⊢
                              calc
                                5040 * (septicCoeff (n + 6) +
                                    sexticCoeff (n + 6)) =
                                  5040 * septicCoeff (n + 6) +
                                    5040 * sexticCoeff (n + 6) :=
                                      Nat.mul_add _ _ _
                                _ = ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) * n +
                                    7 * (720 * sexticCoeff (n + 6)) := by
                                  rw [ih']
                                  ac_rfl
                                _ = ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) * n +
                                    7 * ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) := by
                                  rw [hs]
                                _ = ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) * n +
                                    ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) * 7 := by
                                  ac_rfl
                                _ = ((n + 6) * (n + 5) * (n + 4) *
                                      (n + 3) * (n + 2) * (n + 1)) *
                                    (n + 7) := (Nat.mul_add _ _ _).symm
                                _ = (n + 7) * (n + 6) * (n + 5) *
                                    (n + 4) * (n + 3) * (n + 2) *
                                    (n + 1) := by ac_rfl

/-- Factorial-scaled seventh Pascal coefficient bound. -/
theorem fiveThousandForty_septicCoeff_le_seventh (m : Nat) :
    5040 * septicCoeff m ≤
      m * ((m * m) * ((m * m) * (m * m))) := by
  rw [septicCoeff_fiveThousandForty]
  calc
    m * (m - 1) * (m - 2) * (m - 3) * (m - 4) * (m - 5) *
        (m - 6) ≤ m * m * m * m * m * m * m :=
      Nat.mul_le_mul
        (Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul
              (Nat.mul_le_mul
                (Nat.mul_le_mul (Nat.le_refl m) (Nat.sub_le m 1))
                (Nat.sub_le m 2))
              (Nat.sub_le m 3))
            (Nat.sub_le m 4))
          (Nat.sub_le m 5))
        (Nat.sub_le m 6)
    _ = m * ((m * m) * ((m * m) * (m * m))) := by ac_rfl

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
  · exact h
  · rcases Nat.lt_or_eq_of_le h with hlt | heq
    · have hupper : 2 * D + 1 < 20 * c := by omega
      have hfalse : False := by omega
      exact False.elim hfalse
    · omega

private theorem odd_left_exponent_sq_le_three_den
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
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
  have hsquare : m * m ≤ (c + 1) * (c + 1) := Nat.mul_le_mul hm hm
  have hcsq : c * c ≤ 2 * D + 1 := by
    dsimp only [c, D, thetaWindowCenter, thetaWindowLength]
    exact ChebOrthoMidpointEst.isqrt_sq_le _
  have hright : (c + 1) * (c + 1) ≤ 3 * D := by
    have hexpand : (c + 1) * (c + 1) = c * c + 2 * c + 1 := by
      simp only [Nat.add_mul, Nat.mul_add]
      omega
    rw [hexpand]
    omega
  simpa only [m, D] using Nat.le_trans hsquare hright

private theorem rootSlopeTaylor6_error_numerator_bound
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    (n + 1) * septicCoeff (2 * n + 1) ≤
      (k + 2) * ((k + 2) * ((k + 2) * (k + 2))) := by
  let m := 2 * n + 1
  let D := k + 2
  have hcoeff := fiveThousandForty_septicCoeff_le_seventh m
  have hn1m : n + 1 ≤ m := by
    dsimp only [m]
    omega
  have hm2 : m * m ≤ 3 * D := by
    dsimp only [m, D]
    exact odd_left_exponent_sq_le_three_den hk hn
  have hleft : 5040 * ((n + 1) * septicCoeff m) ≤
      (m * m) * ((m * m) * ((m * m) * (m * m))) := by
    calc
      5040 * ((n + 1) * septicCoeff m) =
          (n + 1) * (5040 * septicCoeff m) := by ac_rfl
      _ ≤ (n + 1) *
          (m * ((m * m) * ((m * m) * (m * m)))) :=
        Nat.mul_le_mul_left (n + 1) hcoeff
      _ ≤ m * (m * ((m * m) * ((m * m) * (m * m)))) :=
        Nat.mul_le_mul_right
          (m * ((m * m) * ((m * m) * (m * m)))) hn1m
      _ = (m * m) * ((m * m) * ((m * m) * (m * m))) := by ac_rfl
  have hfour : (m * m) * ((m * m) * ((m * m) * (m * m))) ≤
      81 * (D * (D * (D * D))) := by
    calc
      (m * m) * ((m * m) * ((m * m) * (m * m))) ≤
          (3 * D) * ((3 * D) * ((3 * D) * (3 * D))) :=
        Nat.mul_le_mul hm2
          (Nat.mul_le_mul hm2 (Nat.mul_le_mul hm2 hm2))
      _ = 81 * (D * (D * (D * D))) := by ac_rfl
  have hscaled : 5040 * ((n + 1) * septicCoeff m) ≤
      5040 * (D * (D * (D * D))) :=
    Nat.le_trans (Nat.le_trans hleft hfour)
      (Nat.mul_le_mul_right (D * (D * (D * D)))
        (by decide : 81 ≤ 5040))
  have hcancel : (n + 1) * septicCoeff m ≤ D * (D * (D * D)) :=
    Nat.le_of_mul_le_mul_left hscaled (by decide)
  simpa only [m, D] using hcancel

/-- On the physical left prefix, the seventh-order root-slope error is at
most `1/(k+2)^3`. -/
theorem lowerSixRootSlopeTaylor6Error_le_invDenCube_large
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    rootSlopeTaylor6Error (harmU k) n ≤
      Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
        (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) := by
  have hnat := rootSlopeTaylor6_error_numerator_bound hk hn
  unfold rootSlopeTaylor6Error harmU unit
  let U : Q' := Q'.mkPos 1 (k + 2) (by omega)
  let X : Q' := Q'.ofNat (n + 1) *
    (Q'.ofNat (septicCoeff (2 * n + 1)) *
      (U * (U * (U * (U * (U * (U * U)))))))
  let T : Q' := Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
    (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega)))
  change X ≤ T
  change X.num * (T.den : Int) ≤ T.num * X.den
  dsimp only [X, T, U]
  simp only [Q'.ofNat_num_cast, Q'.ofNat_den_cast,
    Q'.mkPos_num, Q'.mkPos_den, Q'.mul_num_cast, Q'.mul_den_cast,
    Int.mul_one, Int.one_mul]
  push_cast
  have hnat' :
      ((n + 1) * septicCoeff (2 * n + 1)) *
          ((k + 2) * ((k + 2) * (k + 2))) ≤
        (k + 2) * ((k + 2) * ((k + 2) * ((k + 2) *
          ((k + 2) * ((k + 2) * (k + 2)))))) := by
    have hscaled := Nat.mul_le_mul_right
      ((k + 2) * ((k + 2) * (k + 2))) hnat
    exact Nat.le_trans hscaled (Nat.le_of_eq (by ac_rfl))
  exact_mod_cast hnat'

/-- Production-window upper enclosure with the symbolic seventh-order error
replaced by the harmonic inverse cube. -/
theorem lowerSixThetaRootSlope_le_Taylor6_add_invDenCube_large
    {k n : Nat} (hk : 390 ≤ k) (hn : n ≤ thetaWindowLeft k) :
    thetaRootSlope k n ≤
      rootSlopeTaylor6 (harmU k) n +
        Q'.mkPos 1 ((k + 2) * ((k + 2) * (k + 2)))
          (Nat.mul_pos (by omega) (Nat.mul_pos (by omega) (by omega))) := by
  exact Q'.le_trans' _ _ _
    (lowerSixThetaRootSlope_le_Taylor6_add_error k n)
    (Q'.add_le_add_left _ _ _
      (lowerSixRootSlopeTaylor6Error_le_invDenCube_large hk hn))

#print axioms sexticCoeff_sevenTwenty
#print axioms septicCoeff_fiveThousandForty
#print axioms fiveThousandForty_septicCoeff_le_seventh
#print axioms lowerSixRootSlopeTaylor6Error_le_invDenCube_large
#print axioms lowerSixThetaRootSlope_le_Taylor6_add_invDenCube_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticWindow
