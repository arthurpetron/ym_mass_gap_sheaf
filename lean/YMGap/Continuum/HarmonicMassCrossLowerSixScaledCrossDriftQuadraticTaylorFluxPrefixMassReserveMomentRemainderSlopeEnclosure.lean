/-
Cubic enclosure of the adjacent-root slope.

Substituting the alternating quadratic enclosure of `(1-u)^(2n+1)` into
`n-(n+1)(1-u)^(2n+1)` leaves a nonnegative error bounded explicitly by
`(n+1) * cubicCoeff(2n+1) * u^3`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeEnclosure

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixCubicEnvelope
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pSlopeSplitL : PE :=
  let N : PE := .var 0
  let C : PE := .var 1
  let P : PE := .var 2
  .add N (.neg (.mul C P))

private def pSlopeSplitR : PE :=
  let N : PE := .var 0
  let C : PE := .var 1
  let P : PE := .var 2
  let T : PE := .var 3
  .add (.add N (.neg (.mul C T)))
    (.mul C (.add T (.neg P)))

private theorem pSlopeSplit_normal :
    RingNormaliser.normalize pSlopeSplitL =
      RingNormaliser.normalize pSlopeSplitR := by decide

private theorem slope_split_algebra (N C P T : Q') :
    N + -(C * P) ≈
      (N + -(C * T)) + C * (T + -P) := by
  let rho : Nat → Q' := fun | 0 => N | 1 => C | 2 => P | _ => T
  simpa [pSlopeSplitL, pSlopeSplitR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSlopeSplitL pSlopeSplitR pSlopeSplit_normal rho)

/-- Quadratic Taylor model of the adjacent-root slope at defect `u`. -/
def rootSlopeTaylor2 (u : Q') (n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * oneSubTaylor2 u (2 * n + 1))

/-- Cubic error envelope for that slope model. -/
def rootSlopeTaylor2Error (u : Q') (n : Nat) : Q' :=
  Q'.ofNat (n + 1) *
    (Q'.ofNat (cubicCoeff (2 * n + 1)) * (u * (u * u)))

private theorem rootSlope_exact_split (u : Q') (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≈
      rootSlopeTaylor2 u n +
        Q'.ofNat (n + 1) *
          (oneSubTaylor2 u (2 * n + 1) +
            -qpow ((1 : Q') + -u) (2 * n + 1)) := by
  unfold rootSlopeTaylor2
  exact slope_split_algebra _ _ _ _

private theorem rootSlope_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    (0 : Q') ≤ Q'.ofNat (n + 1) *
      (oneSubTaylor2 u (2 * n + 1) +
        -qpow ((1 : Q') + -u) (2 * n + 1)) := by
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_oneSub_taylor2_error_nonnegative hu0 hu1 _)

private theorem rootSlope_error_le
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat (n + 1) *
        (oneSubTaylor2 u (2 * n + 1) +
          -qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor2Error u n := by
  unfold rootSlopeTaylor2Error
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1))
    (qpow_oneSub_taylor2_error_le_cubic hu0 hu1 _)
    (HeatKernelRGStep.zero_le_ofNat _)

/-- The Taylor slope model is a lower bound for the exact slope. -/
theorem rootSlopeTaylor2_le_exact
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    rootSlopeTaylor2 u n ≤
      Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) := by
  let E := Q'.ofNat (n + 1) *
    (oneSubTaylor2 u (2 * n + 1) +
      -qpow ((1 : Q') + -u) (2 * n + 1))
  have hE0 : (0 : Q') ≤ E := by
    dsimp only [E]
    exact rootSlope_error_nonnegative hu0 hu1 n
  have hadd := Q'.add_le_self_of_nonneg (rootSlopeTaylor2 u n) E hE0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm (rootSlope_exact_split u n)))

/-- The exact slope exceeds its Taylor model by at most the cubic envelope. -/
theorem rootSlope_exact_le_taylor2_add_error
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor2 u n + rootSlopeTaylor2Error u n := by
  have herr := rootSlope_error_le hu0 hu1 n
  have hadd := Q'.add_le_add_left (rootSlopeTaylor2 u n) _ _ herr
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rootSlope_exact_split u n)) hadd

/-- Actual harmonic root slope, lower enclosure. -/
theorem lowerSixThetaRootSlopeTaylor2_le (k n : Nat) :
    rootSlopeTaylor2 (harmU k) n ≤ thetaRootSlope k n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlopeTaylor2_le_exact (harmU_nonneg k) (harmU_le_one k) n

/-- Actual harmonic root slope, upper enclosure. -/
theorem lowerSixThetaRootSlope_le_Taylor2_add_error (k n : Nat) :
    thetaRootSlope k n ≤
      rootSlopeTaylor2 (harmU k) n +
        rootSlopeTaylor2Error (harmU k) n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlope_exact_le_taylor2_add_error
    (harmU_nonneg k) (harmU_le_one k) n

#print axioms rootSlopeTaylor2_le_exact
#print axioms rootSlope_exact_le_taylor2_add_error
#print axioms lowerSixThetaRootSlopeTaylor2_le
#print axioms lowerSixThetaRootSlope_le_Taylor2_add_error

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeEnclosure
