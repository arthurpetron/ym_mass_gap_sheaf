/-
Quintic enclosure of the adjacent-root slope.

This is the high-precision companion to the quadratic slope model.  Its
error is the exact fifth Pascal coefficient times `u^5`, small enough to be
transported through the finite-Hermite `D^4` clearing.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuintic

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylorFive
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

/-- Fourth-order Taylor model of the adjacent-root slope. -/
def rootSlopeTaylor4 (u : Q') (n : Nat) : Q' :=
  Q'.ofNat n +
    -(Q'.ofNat (n + 1) * oneSubTaylor4 u (2 * n + 1))

/-- Exact quintic error envelope for the fourth-order slope model. -/
def rootSlopeTaylor4Error (u : Q') (n : Nat) : Q' :=
  Q'.ofNat (n + 1) *
    (Q'.ofNat (quinticCoeff (2 * n + 1)) *
      (u * (u * (u * (u * u)))))

private theorem rootSlope_exact_split (u : Q') (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≈
      rootSlopeTaylor4 u n +
        Q'.ofNat (n + 1) *
          (oneSubTaylor4 u (2 * n + 1) +
            -qpow ((1 : Q') + -u) (2 * n + 1)) := by
  unfold rootSlopeTaylor4
  exact slope_split_algebra _ _ _ _

private theorem rootSlope_error_nonnegative
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    (0 : Q') ≤ Q'.ofNat (n + 1) *
      (oneSubTaylor4 u (2 * n + 1) +
        -qpow ((1 : Q') + -u) (2 * n + 1)) := by
  exact Q'.mul_nonneg _ _ (HeatKernelRGStep.zero_le_ofNat _)
    (qpow_oneSub_taylor4_error_nonnegative hu0 hu1 _)

private theorem rootSlope_error_le
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat (n + 1) *
        (oneSubTaylor4 u (2 * n + 1) +
          -qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor4Error u n := by
  unfold rootSlopeTaylor4Error
  exact Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (n + 1))
    (qpow_oneSub_taylor4_error_le_quintic hu0 hu1 _)
    (HeatKernelRGStep.zero_le_ofNat _)

/-- The fourth-order Taylor slope is a lower bound for the exact slope. -/
theorem rootSlopeTaylor4_le_exact
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    rootSlopeTaylor4 u n ≤
      Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) := by
  let E := Q'.ofNat (n + 1) *
    (oneSubTaylor4 u (2 * n + 1) +
      -qpow ((1 : Q') + -u) (2 * n + 1))
  have hE0 : (0 : Q') ≤ E := by
    dsimp only [E]
    exact rootSlope_error_nonnegative hu0 hu1 n
  have hadd := Q'.add_le_self_of_nonneg (rootSlopeTaylor4 u n) E hE0
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.eqv_symm (rootSlope_exact_split u n)))

/-- The exact slope exceeds its fourth-order Taylor model by at most the
quintic Pascal envelope. -/
theorem rootSlope_exact_le_taylor4_add_error
    {u : Q'} (hu0 : (0 : Q') ≤ u) (hu1 : u ≤ (1 : Q')) (n : Nat) :
    Q'.ofNat n +
        -(Q'.ofNat (n + 1) * qpow ((1 : Q') + -u) (2 * n + 1)) ≤
      rootSlopeTaylor4 u n + rootSlopeTaylor4Error u n := by
  have herr := rootSlope_error_le hu0 hu1 n
  have hadd := Q'.add_le_add_left (rootSlopeTaylor4 u n) _ _ herr
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (rootSlope_exact_split u n)) hadd

/-- Harmonic root slope, fourth-order lower enclosure. -/
theorem lowerSixThetaRootSlopeTaylor4_le (k n : Nat) :
    rootSlopeTaylor4 (harmU k) n ≤ thetaRootSlope k n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlopeTaylor4_le_exact (harmU_nonneg k) (harmU_le_one k) n

/-- Harmonic root slope, fourth-order upper enclosure. -/
theorem lowerSixThetaRootSlope_le_Taylor4_add_error (k n : Nat) :
    thetaRootSlope k n ≤
      rootSlopeTaylor4 (harmU k) n +
        rootSlopeTaylor4Error (harmU k) n := by
  unfold thetaRootSlope harmW ReciprocalBernoulliUpper.oneSub
  exact rootSlope_exact_le_taylor4_add_error
    (harmU_nonneg k) (harmU_le_one k) n

#print axioms rootSlopeTaylor4_le_exact
#print axioms rootSlope_exact_le_taylor4_add_error
#print axioms lowerSixThetaRootSlopeTaylor4_le
#print axioms lowerSixThetaRootSlope_le_Taylor4_add_error

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeQuintic
