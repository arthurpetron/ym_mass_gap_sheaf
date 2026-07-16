/-
Closed quadratic normal form for the adjacent-root slope.

The recursive Pascal coefficient in the alternating Taylor enclosure is
eliminated exactly at the odd exponent `2n+1`.  Combined with the uniform
cubic window bound, this sandwiches the physical slope between one explicit
quadratic polynomial and that same polynomial plus `1/40`.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeWindow

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopePolynomial

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMoment
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderOneSubTaylor
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeEnclosure
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeWindow
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftRemainderPayment
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SummableInverseSquare

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pSlopeTaylorExpandL : PE :=
  let N : PE := .var 0
  let P : PE := .var 1
  let M : PE := .var 2
  let C : PE := .var 3
  let u : PE := .var 4
  .add N
    (.neg (.mul P
      (.add
        (.add (.const 1) (.neg (.mul M u)))
        (.mul C (.mul u u)))))

private def pSlopeTaylorExpandR : PE :=
  let N : PE := .var 0
  let P : PE := .var 1
  let M : PE := .var 2
  let C : PE := .var 3
  let u : PE := .var 4
  .add
    (.add
      (.add N (.neg P))
      (.mul (.mul P M) u))
    (.neg (.mul (.mul P C) (.mul u u)))

private theorem pSlopeTaylorExpand_normal :
    RingNormaliser.normalize pSlopeTaylorExpandL =
      RingNormaliser.normalize pSlopeTaylorExpandR := by decide

private theorem slopeTaylor_expand_algebra (N P M C u : Q') :
    N + -(P * (((1 : Q') + -(M * u)) + C * (u * u))) ≈
      ((N + -P) + (P * M) * u) +
        -((P * C) * (u * u)) := by
  let rho : Nat → Q' := fun
    | 0 => N | 1 => P | 2 => M | 3 => C | _ => u
  simpa [pSlopeTaylorExpandL, pSlopeTaylorExpandR,
    RingNormaliser.eval, rho] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSlopeTaylorExpandL pSlopeTaylorExpandR
      pSlopeTaylorExpand_normal rho)

/-- Odd Pascal coefficients have the subtraction-free closed form
`choose(2n+1,2)=n(2n+1)`. -/
theorem lowerSixQuadraticCoeff_odd (n : Nat) :
    lowerSixQuadraticCoeff (2 * n + 1) = n * (2 * n + 1) := by
  have h := lowerSixQuadraticCoeff_double (2 * n + 1)
  have hsub : 2 * n + 1 - 1 = 2 * n := by omega
  rw [hsub] at h
  have hscaled :
      2 * lowerSixQuadraticCoeff (2 * n + 1) =
        2 * (n * (2 * n + 1)) := by
    calc
      2 * lowerSixQuadraticCoeff (2 * n + 1) =
          (2 * n + 1) * (2 * n) := h
      _ = 2 * (n * (2 * n + 1)) := by ac_rfl
  exact Nat.eq_of_mul_eq_mul_left (by omega) hscaled

/-- Explicit quadratic model of the physical adjacent-root slope. -/
def rootSlopeQuadraticPolynomial (u : Q') (n : Nat) : Q' :=
  let N := Q'.ofNat n
  let P := Q'.ofNat (n + 1)
  let M := Q'.ofNat (2 * n + 1)
  ((N + -P) + (P * M) * u) +
    -((P * (N * M)) * (u * u))

/-- Exact removal of the recursive Pascal coefficient from the Taylor
slope model. -/
theorem rootSlopeTaylor2_eqv_quadraticPolynomial (u : Q') (n : Nat) :
    rootSlopeTaylor2 u n ≈ rootSlopeQuadraticPolynomial u n := by
  let N := Q'.ofNat n
  let P := Q'.ofNat (n + 1)
  let M := Q'.ofNat (2 * n + 1)
  let C := Q'.ofNat (lowerSixQuadraticCoeff (2 * n + 1))
  have hcoeffNat := lowerSixQuadraticCoeff_odd n
  have hcoeff : C ≈ N * M := by
    dsimp only [C, N, M]
    rw [hcoeffNat]
    exact HeatKernelRGStep.ofNat_mul_eqv n (2 * n + 1)
  have hraw : rootSlopeTaylor2 u n ≈
      ((N + -P) + (P * M) * u) +
        -((P * C) * (u * u)) := by
    unfold rootSlopeTaylor2 oneSubTaylor2
    dsimp only [N, P, M, C]
    exact slopeTaylor_expand_algebra _ _ _ _ _
  have hPC : P * C ≈ P * (N * M) :=
    Q'.mul_eqv_congr_left P _ _ hcoeff
  have hlast : -((P * C) * (u * u)) ≈
      -((P * (N * M)) * (u * u)) :=
    Q'.neg_eqv_congr _ _
      (Q'.mul_eqv_congr_right _ _ (u * u) hPC)
  unfold rootSlopeQuadraticPolynomial
  dsimp only [N, P, M, C] at hraw hlast ⊢
  exact Q'.eqv_trans _ _ _ hraw
    (Q'.add_eqv_congr_left _ _ _ hlast)

/-- The explicit quadratic polynomial is a lower enclosure of the exact
harmonic root slope at every scale. -/
theorem lowerSixRootSlopeQuadraticPolynomial_le (k n : Nat) :
    rootSlopeQuadraticPolynomial (harmU k) n ≤ thetaRootSlope k n := by
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv
      (rootSlopeTaylor2_eqv_quadraticPolynomial (harmU k) n))
    (lowerSixThetaRootSlopeTaylor2_le k n)

/-- On the production prefix, the exact root slope is at most `1/40` above
its explicit quadratic polynomial. -/
theorem lowerSixThetaRootSlope_le_quadraticPolynomial_add_oneFortieth_large
    {k n : Nat} (hk : 8189 ≤ k) (hn : n ≤ thetaWindowRight k) :
    thetaRootSlope k n ≤
      rootSlopeQuadraticPolynomial (harmU k) n +
        Q'.mkPos 1 40 (by decide) := by
  have hslope := lowerSixThetaRootSlope_le_Taylor2_add_error k n
  have herr := lowerSixRootSlopeTaylor2Error_le_oneFortieth_large hk hn
  have hadd := Q'.add_le_add_left (rootSlopeTaylor2 (harmU k) n)
    _ _ herr
  have hpoly := rootSlopeTaylor2_eqv_quadraticPolynomial (harmU k) n
  have hreplace :
      rootSlopeTaylor2 (harmU k) n + Q'.mkPos 1 40 (by decide) ≈
        rootSlopeQuadraticPolynomial (harmU k) n +
          Q'.mkPos 1 40 (by decide) :=
    Q'.add_eqv_congr_right _ _ _ hpoly
  exact Q'.le_trans' _ _ _ hslope
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hreplace))

#print axioms lowerSixQuadraticCoeff_odd
#print axioms rootSlopeTaylor2_eqv_quadraticPolynomial
#print axioms lowerSixRootSlopeQuadraticPolynomial_le
#print axioms lowerSixThetaRootSlope_le_quadraticPolynomial_add_oneFortieth_large

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopePolynomial
