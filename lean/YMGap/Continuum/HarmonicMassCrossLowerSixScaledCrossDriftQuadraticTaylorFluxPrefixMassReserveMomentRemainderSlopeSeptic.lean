/-
Seventh-order enclosure of the adjacent-root slope.

The exact slope is trapped between the slope induced by the even sixth
power truncation and that model plus the exact seventh Pascal error.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorSeven
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pSlopeSplitL : PE :=
  .add (.var 0) (.neg (.mul (.var 1) (.var 2)))

private def pSlopeSplitR : PE :=
  .add
    (.add (.var 0) (.neg (.mul (.var 1) (.var 3))))
    (.mul (.var 1) (.add (.var 3) (.neg (.var 2))))

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

/-- Sixth-order Taylor model of the adjacent-root slope. -/
def rootSlopeTaylor6 (u : Q') (n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * oneSubTaylor6 u (2 * n + 1))

/-- Exact seventh-order error envelope for the sixth-order slope model. -/
def rootSlopeTaylor6Error (u : Q') (n : Nat) : Q' :=
  Q'.ofNat (n + 1) *
    (Q'.ofNat (septicCoeff (2 * n + 1)) *
      (u * (u * (u * (u * (u * (u * u)))))))

private theorem rootSlope_exact_split (u : Q') (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≈
      rootSlopeTaylor6 u n +
        Q'.ofNat (n + 1) *
          (oneSubTaylor6 u (2 * n + 1) +
            -qpow ((1 : Q') + -u) (2 * n + 1)) := by
  unfold rootSlopeTaylor6
  exact slope_split_algebra _ _ _ _

private theorem rootSlope_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    (0 : Q') ≤ Q'.ofNat (n + 1) *
      (oneSubTaylor6 u (2 * n + 1) +
        -qpow ((1 : Q') + -u) (2 * n + 1)) :=
  Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_oneSub_taylor6_error_nonnegative hu0 hu1 _)

private theorem rootSlope_error_le
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat (n + 1) *
        (oneSubTaylor6 u (2 * n + 1) +
          -qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor6Error u n := by
  unfold rootSlopeTaylor6Error
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1))
    (qpow_oneSub_taylor6_error_le_septic hu0 hu1 _)
    (HeatKernelRGStep.zero_le_ofNat _)

/-- The sixth-order Taylor slope is a lower bound for the exact slope. -/
theorem rootSlopeTaylor6_le_exact
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    rootSlopeTaylor6 u n ≤
      Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) := by
  let E := Q'.ofNat (n + 1) *
    (oneSubTaylor6 u (2 * n + 1) +
      -qpow ((1 : Q') + -u) (2 * n + 1))
  have hE0 : (0 : Q') ≤ E := rootSlope_error_nonnegative hu0 hu1 n
  have hadd := Q'.add_le_self_of_nonneg (rootSlopeTaylor6 u n) E hE0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm (rootSlope_exact_split u n)))

/-- The exact slope exceeds its sixth-order model by at most the seventh
Pascal envelope. -/
theorem rootSlope_exact_le_taylor6_add_error
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor6 u n + rootSlopeTaylor6Error u n := by
  have herr := rootSlope_error_le hu0 hu1 n
  have hadd := Q'.add_le_add_left (rootSlopeTaylor6 u n) _ _ herr
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rootSlope_exact_split u n)) hadd

/-- Harmonic root slope, sixth-order lower enclosure. -/
theorem lowerSixThetaRootSlopeTaylor6_le (k n : Nat) :
    rootSlopeTaylor6 (harmU k) n ≤ thetaRootSlope k n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlopeTaylor6_le_exact (harmU_nonneg k) (harmU_le_one k) n

/-- Harmonic root slope, sixth-order upper enclosure. -/
theorem lowerSixThetaRootSlope_le_Taylor6_add_error (k n : Nat) :
    thetaRootSlope k n ≤
      rootSlopeTaylor6 (harmU k) n +
        rootSlopeTaylor6Error (harmU k) n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlope_exact_le_taylor6_add_error
    (harmU_nonneg k) (harmU_le_one k) n

#print axioms rootSlopeTaylor6_le_exact
#print axioms rootSlope_exact_le_taylor6_add_error
#print axioms lowerSixThetaRootSlopeTaylor6_le
#print axioms lowerSixThetaRootSlope_le_Taylor6_add_error

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSeptic
