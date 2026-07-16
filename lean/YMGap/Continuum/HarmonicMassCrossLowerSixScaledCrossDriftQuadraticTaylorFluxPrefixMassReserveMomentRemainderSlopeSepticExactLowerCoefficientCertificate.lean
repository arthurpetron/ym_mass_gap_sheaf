/-
Reflective coefficient algebra for the mode-sensitive septic lower
polynomial.

After clearing only positive denominators, substitute

  N = M + 8,  D = 2 N^2 + Z.

The resulting bivariate integer polynomial has nonnegative coefficients.
This file records finite symbolic coefficient facts in the kernel without
importing measured constants.  Low modes use `D=8191+X`; the larger high-mode
table is split separately so each compilation stays within the normal kernel
stack budget.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLower
import YMGap.Continuum.CoreBResidualSimplex

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate

set_option maxHeartbeats 100000000
set_option maxRecDepth 1000000

open YMGap.Continuum.CoreBResidualSimplex

private abbrev PE := RingNormaliser.PolyExpr

private def pc (z : Int) : PE := .const z
private def pv (i : Nat) : PE := .var i
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n
private def psub (a b : PE) : PE := padd a (pneg b)

private def pFall (x : PE) : Nat → PE
  | 0 => pc 1
  | r + 1 => pmul (pFall x r) (psub x (pc r))

/-- `720 D^6` times the sixth-order root-slope model. -/
private def pSlopeScaled (D N : PE) : PE :=
  let m := padd (pmul (pc 2) N) (pc 1)
  let t6 :=
    padd
      (padd
        (padd
          (padd
            (padd
              (pmul (pc 720) (ppow D 6))
              (pneg (pmul (pmul (pc 720) m) (ppow D 5))))
            (pmul (pmul (pc 360) (pFall m 2)) (ppow D 4)))
          (pneg (pmul (pmul (pc 120) (pFall m 3)) (ppow D 3))))
        (pmul (pmul (pc 30) (pFall m 4)) (ppow D 2)))
      (padd
        (pneg (pmul (pmul (pc 6) (pFall m 5)) D))
        (pFall m 6))
  psub (pmul (pmul (pc 720) N) (ppow D 6))
    (pmul (padd N (pc 1)) t6)

/-- Twice the numerator of the quadratic drift factor, over
`2 (D^2-1)^4`. -/
private def pDriftFactorScaled (D N : PE) : PE :=
  let d := psub (ppow D 2) (pc 1)
  let r := padd (pmul (pc 2) d) (pc 1)
  let N2 := ppow N 2
  padd
    (padd
      (pmul (pc 2) (ppow d 4))
      (pmul (pmul (pmul (pc 2) N2) r) (ppow d 2)))
    (pmul (pmul N2 (psub N2 (pc 1))) (ppow r 2))

private def pInnerNextScaled (D N : PE) : PE :=
  let A := padd N (pc 1)
  let m := padd (pmul (pc 2) N) (pc 1)
  let T := pSlopeScaled D N
  padd
    (padd
      (pmul (pc 28) (ppow T 2))
      (pneg (pmul (pmul (pmul (pc 11520) A) (pFall m 7))
        (ppow D 5))))
    (pneg (pmul (pmul (pmul (pc 3628800) (ppow N 2))
      (padd (pmul (pc 12) (ppow D 2)) (pc 1))) (ppow D 9)))

private def pInnerOldScaled (D N : PE) : PE :=
  let A := padd N (pc 1)
  let m := padd (pmul (pc 2) N) (pc 1)
  let T := pSlopeScaled D N
  padd
    (padd
      (pmul (pc 28) (ppow T 2))
      (pmul (pmul (pmul (pc 8640) A) (pFall m 7)) (ppow D 5)))
    (pneg (pmul (pmul (pmul (pc 3628800) (ppow N 2))
      (padd (pmul (pc 12) (ppow D 2)) (pc 1))) (ppow D 9)))

private def pCarrierScaled (D N : PE) : PE :=
  let D1 := padd D (pc 1)
  let d := psub (ppow D 2) (pc 1)
  psub
    (pmul (pmul (pDriftFactorScaled D N) (pInnerNextScaled D1 N))
      (ppow D 11))
    (pmul (pmul (pmul (pc 2) (ppow d 4)) (pInnerOldScaled D N))
      (ppow D1 11))

private def pFlux (D N : PE) : PE :=
  padd
    (padd
      (padd
        (padd
          (padd
            (padd
              (padd
                (padd
                  (pmul (pmul (pc 192) N) (ppow D 4))
                  (pmul (pmul (pc 384) (ppow N 3)) (ppow D 3)))
                (pneg (pmul (pmul (pc 6) N) (ppow D 3))))
              (pneg (pmul (pmul (pc 384) (ppow N 5)) (ppow D 2))))
            (pmul (pmul (pc 576) (ppow N 4)) (ppow D 2)))
          (pmul (pmul (pc 184) (ppow N 3)) (ppow D 2)))
        (pmul (pmul (pc 224) (ppow N 5)) D))
      (pneg (pmul (pc 256) (ppow N 7))))
    (padd (pmul (pc 576) (ppow N 6)) (pmul (pc 3) (ppow D 3)))

/-- Positive common denominator
`2*3628800*(D^2-1)^4*D^12*(D+1)^11`. -/
private def pCommonDen (D : PE) : PE :=
  pmul
    (pmul
      (pmul (pc 7257600) (ppow (psub (ppow D 2) (pc 1)) 4))
      (ppow D 12))
    (ppow (padd D (pc 1)) 11)

/-- Cleared integer numerator of the mode-sensitive Taylor-six lower
polynomial. -/
def pExactLowerNumerator (D N : PE) : PE :=
  let A := padd N (pc 1)
  let D1 := padd D (pc 1)
  let d := psub (ppow D 2) (pc 1)
  let T := pSlopeScaled D N
  let main :=
    padd
      (pmul (pmul (pc 48) (ppow D 5)) (pCarrierScaled D N))
      (pmul (psub (pFlux D N) (pmul (pc 6) (ppow D 3)))
        (pCommonDen D))
  let oldFluxScaled := psub (pmul (pmul (pc 720) N) (ppow D 6)) T
  psub
    (pmul (ppow A 2) main)
    (pmul
      (pmul
        (pmul (pc 14) (ppow d 4))
        (ppow D1 11))
      (pmul (ppow oldFluxScaled 2) (pFlux D (padd N (pc 1)))))

/-- High-mode square-root-slack substitution `N=M+8`, `D=2N^2+Z`. -/
def pExactLowerHigh : PE :=
  let M := pv 0
  let Z := pv 1
  let N := padd M (pc 8)
  let D := padd (pmul (pc 2) (ppow N 2)) Z
  pExactLowerNumerator D N

/-- Low-mode large-scale substitution `D=8191+X` at a fixed mode. -/
def pExactLowerLow (n : Nat) : PE :=
  pExactLowerNumerator (padd (pc 8191) (pv 0)) (pc n)

/-- The eight low-mode numerator polynomials have nonnegative coefficients
after the production-scale shift `D=8191+X`. -/
theorem pExactLowerLow_coefficients_nonnegative :
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 0)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 1)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 2)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 3)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 4)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 5)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 6)) = true ∧
    RawCoefficientsNonnegative (fastNormalize (pExactLowerLow 7)) = true := by
  decide

#print axioms pExactLowerLow_coefficients_nonnegative

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticExactLowerCoefficientCertificate
