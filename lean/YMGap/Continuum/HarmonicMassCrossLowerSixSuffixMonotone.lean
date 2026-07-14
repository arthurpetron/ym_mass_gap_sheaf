/-
Polynomial monotonicity engine for the lower-six right suffix.

After clearing the harmonic denominator cube, the right-cell slack is a
polynomial in the denominator `D` and mode `N`.  On the natural suffix range
`D >= 50`, `N >= 13`, `N^2 >= 3D`, its forward difference is a polynomial
with manifestly nonnegative coefficients.  This file records that exact
identity and positivity in the constructive rational substrate.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixTwoSidedWindow
import YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindowCubicFullEndpoint

local infix:50 " ≈ " => Q'.eqv

def lowerSixRightRawDen (D N : Q') : Q' :=
  D + (Q'.ofNat 2 * N + 1)

def lowerSixRightRawNum (D N : Q') : Q' :=
  N * lowerSixRightRawDen D N + -((N + 1) * D)

def lowerSixRightRawSlack (D N : Q') : Q' :=
  (Q'.ofNat 4 *
      RingNormaliser.qpow (lowerSixRightRawNum D N) 2) *
      RingNormaliser.qpow D 3 +
    -((Q'.ofNat 12 * RingNormaliser.qpow D 2 + 1) *
      RingNormaliser.qpow N 2 *
      RingNormaliser.qpow (lowerSixRightRawDen D N) 2)

/-- Expanded forward difference of the cleared raw slack. -/
def lowerSixRightRawDeltaPoly (D N : Q') : Q' :=
  (Q'.ofNat 64 * RingNormaliser.qpow D 3 +
      -(Q'.ofNat 192 * RingNormaliser.qpow D 2) + -(Q'.ofNat 16)) *
      RingNormaliser.qpow N 3 +
    -((Q'.ofNat 432 * RingNormaliser.qpow D 2 + Q'.ofNat 12 * D +
      Q'.ofNat 36) * RingNormaliser.qpow N 2) +
    -((Q'.ofNat 56 * RingNormaliser.qpow D 4 +
      Q'.ofNat 72 * RingNormaliser.qpow D 3 +
      Q'.ofNat 362 * RingNormaliser.qpow D 2 + Q'.ofNat 16 * D +
      Q'.ofNat 30) * N) +
    -(Q'.ofNat 36 * RingNormaliser.qpow D 4 +
      Q'.ofNat 36 * RingNormaliser.qpow D 3 +
      Q'.ofNat 109 * RingNormaliser.qpow D 2 + Q'.ofNat 6 * D + Q'.ofNat 9)

/-- Positive coefficient of the square-slack variable. -/
def lowerSixRightDeltaSquareCoeff (x t : Q') : Q' :=
  t * qNatPoly x [7519984, 460800, 9408, 64] +
    qNatPoly x [96679156, 5947188, 121872, 832]

/-- Manifestly nonnegative normal form of the forward slack difference. -/
def lowerSixRightDeltaPositive (x t z : Q') : Q' :=
  t * qNatPoly x [768091770, 63103736, 1942438, 26552, 136] +
    qNatPoly x [9593324801, 792343954, 24511749, 336644, 1732] +
    z * lowerSixRightDeltaSquareCoeff x t

private abbrev PE := RingNormaliser.PolyExpr

private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pNatPoly (x : PE) : List Nat → PE
  | [] => pc 0
  | a :: as => padd (pc (Int.ofNat a)) (pmul x (pNatPoly x as))

private def pRawDen (D N : PE) : PE :=
  padd D (padd (pmul (pc 2) N) (pc 1))

private def pRawNum (D N : PE) : PE :=
  padd (pmul N (pRawDen D N))
    (pneg (pmul (padd N (pc 1)) D))

private def pRawSlack (D N : PE) : PE :=
  padd
    (pmul (pmul (pc 4) (ppow (pRawNum D N) 2)) (ppow D 3))
    (pneg (pmul
      (pmul (padd (pmul (pc 12) (ppow D 2)) (pc 1)) (ppow N 2))
      (ppow (pRawDen D N) 2)))

private def pSquareCoeff (x t : PE) : PE :=
  padd
    (pmul t (pNatPoly x [7519984, 460800, 9408, 64]))
    (pNatPoly x [96679156, 5947188, 121872, 832])

private def pPositive (x t z : PE) : PE :=
  padd
    (padd
      (pmul t (pNatPoly x
        [768091770, 63103736, 1942438, 26552, 136]))
      (pNatPoly x
        [9593324801, 792343954, 24511749, 336644, 1732]))
    (pmul z (pSquareCoeff x t))

private def pDeltaPoly (D N : PE) : PE :=
  padd
    (padd
      (padd
        (pmul
          (padd (padd
            (pmul (pc 64) (ppow D 3))
            (pneg (pmul (pc 192) (ppow D 2))))
            (pneg (pc 16)))
          (ppow N 3))
        (pneg (pmul
          (padd (padd (pmul (pc 432) (ppow D 2))
            (pmul (pc 12) D)) (pc 36))
          (ppow N 2))))
      (pneg (pmul
        (padd (padd (padd (padd
          (pmul (pc 56) (ppow D 4))
          (pmul (pc 72) (ppow D 3)))
          (pmul (pc 362) (ppow D 2)))
          (pmul (pc 16) D)) (pc 30))
        N)))
    (pneg (padd (padd (padd (padd
      (pmul (pc 36) (ppow D 4))
      (pmul (pc 36) (ppow D 3)))
      (pmul (pc 109) (ppow D 2)))
      (pmul (pc 6) D)) (pc 9)))

private def pRawDeltaL : PE :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  padd (pRawSlack D (padd N (pc 1))) (pneg (pRawSlack D N))

private def pRawDeltaR : PE :=
  pDeltaPoly (RingNormaliser.PolyExpr.var 0)
    (RingNormaliser.PolyExpr.var 1)

private def pSubDeltaL : PE :=
  let x := RingNormaliser.PolyExpr.var 0
  let t := RingNormaliser.PolyExpr.var 1
  pDeltaPoly (padd (pc 50) x) (padd (pc 13) t)

private def pSubDeltaR : PE :=
  let x := RingNormaliser.PolyExpr.var 0
  let t := RingNormaliser.PolyExpr.var 1
  let z := RingNormaliser.PolyExpr.var 2
  let D := padd (pc 50) x
  let N := padd (pc 13) t
  padd (pPositive x t z)
    (pmul (pSquareCoeff x t)
      (padd (ppow N 2)
        (pneg (padd (pmul (pc 3) D) z))))

private theorem pRawDelta_normal :
    RingNormaliser.normalize pRawDeltaL =
      RingNormaliser.normalize pRawDeltaR := by decide

private theorem pSubDelta_normal :
    RingNormaliser.normalize pSubDeltaL =
      RingNormaliser.normalize pSubDeltaR := by decide

/-- Exact forward-difference identity.  The final product vanishes when
`N^2 = 3D + z`; the remaining term has only nonnegative coefficients. -/
theorem lowerSixRightRawSlack_delta_identity (x t z : Q') :
    lowerSixRightRawSlack (Q'.ofNat 50 + x)
          ((Q'.ofNat 13 + t) + 1) +
        -lowerSixRightRawSlack (Q'.ofNat 50 + x)
          (Q'.ofNat 13 + t) ≈
      lowerSixRightDeltaPositive x t z +
        lowerSixRightDeltaSquareCoeff x t *
          (RingNormaliser.qpow (Q'.ofNat 13 + t) 2 +
            -((Q'.ofNat 3 * (Q'.ofNat 50 + x)) + z)) := by
  have hraw :
      lowerSixRightRawSlack (Q'.ofNat 50 + x)
            ((Q'.ofNat 13 + t) + 1) +
          -lowerSixRightRawSlack (Q'.ofNat 50 + x)
            (Q'.ofNat 13 + t) ≈
        lowerSixRightRawDeltaPoly (Q'.ofNat 50 + x)
          (Q'.ofNat 13 + t) := by
    simpa [pRawDeltaL, pRawDeltaR, pRawSlack, pRawNum, pRawDen,
      pDeltaPoly, pc, padd, pmul, pneg, ppow,
      lowerSixRightRawSlack, lowerSixRightRawNum, lowerSixRightRawDen,
      lowerSixRightRawDeltaPoly, RingNormaliser.eval] using
      (RingNormaliser.poly_identity_of_normal_eq
        pRawDeltaL pRawDeltaR pRawDelta_normal
        (fun | 0 => Q'.ofNat 50 + x | _ => Q'.ofNat 13 + t))
  have hsub :
      lowerSixRightRawDeltaPoly (Q'.ofNat 50 + x)
          (Q'.ofNat 13 + t) ≈
        lowerSixRightDeltaPositive x t z +
          lowerSixRightDeltaSquareCoeff x t *
            (RingNormaliser.qpow (Q'.ofNat 13 + t) 2 +
              -((Q'.ofNat 3 * (Q'.ofNat 50 + x)) + z)) := by
    simpa [pSubDeltaL, pSubDeltaR, pDeltaPoly, pPositive,
      pSquareCoeff, pNatPoly, pc, padd, pmul, pneg, ppow,
      lowerSixRightRawDeltaPoly, lowerSixRightDeltaPositive,
      lowerSixRightDeltaSquareCoeff, RingNormaliser.eval] using
      (RingNormaliser.poly_identity_of_normal_eq
        pSubDeltaL pSubDeltaR pSubDelta_normal
        (fun | 0 => x | 1 => t | _ => z))
  exact Q'.eqv_trans _ _ _ hraw hsub

theorem lowerSixRightDeltaSquareCoeff_nonnegative {x t : Q'}
    (hx : (0 : Q') ≤ x) (ht : (0 : Q') ≤ t) :
    (0 : Q') ≤ lowerSixRightDeltaSquareCoeff x t := by
  unfold lowerSixRightDeltaSquareCoeff
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ ht (qNatPoly_nonnegative hx _))
    (qNatPoly_nonnegative hx _)

theorem lowerSixRightDeltaPositive_nonnegative {x t z : Q'}
    (hx : (0 : Q') ≤ x) (ht : (0 : Q') ≤ t)
    (hz : (0 : Q') ≤ z) :
    (0 : Q') ≤ lowerSixRightDeltaPositive x t z := by
  unfold lowerSixRightDeltaPositive
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ ht (qNatPoly_nonnegative hx _))
      (qNatPoly_nonnegative hx _))
    (Q'.mul_nonneg _ _ hz
      (lowerSixRightDeltaSquareCoeff_nonnegative hx ht))

/-- Under the square-slack identity, the cleared right-cell slack is
nondecreasing by one mode. -/
theorem lowerSixRightRawSlack_monotone_step
    {x t z : Q'}
    (hx : (0 : Q') ≤ x) (ht : (0 : Q') ≤ t)
    (hz : (0 : Q') ≤ z)
    (hsq : RingNormaliser.qpow (Q'.ofNat 13 + t) 2 ≈
      Q'.ofNat 3 * (Q'.ofNat 50 + x) + z) :
    lowerSixRightRawSlack (Q'.ofNat 50 + x) (Q'.ofNat 13 + t) ≤
      lowerSixRightRawSlack (Q'.ofNat 50 + x)
        ((Q'.ofNat 13 + t) + 1) := by
  have hzero :
      RingNormaliser.qpow (Q'.ofNat 13 + t) 2 +
          -((Q'.ofNat 3 * (Q'.ofNat 50 + x)) + z) ≈ (0 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _ (Q'.eqv_symm hsq)))
      (Q'.add_neg_self_eqv _)
  have hid := lowerSixRightRawSlack_delta_identity x t z
  have hdelta : (0 : Q') ≤
      lowerSixRightRawSlack (Q'.ofNat 50 + x)
          ((Q'.ofNat 13 + t) + 1) +
        -lowerSixRightRawSlack (Q'.ofNat 50 + x)
          (Q'.ofNat 13 + t) := by
    have hpos := lowerSixRightDeltaPositive_nonnegative hx ht hz
    have hright :
        lowerSixRightDeltaPositive x t z +
            lowerSixRightDeltaSquareCoeff x t *
              (RingNormaliser.qpow (Q'.ofNat 13 + t) 2 +
                -((Q'.ofNat 3 * (Q'.ofNat 50 + x)) + z)) ≈
          lowerSixRightDeltaPositive x t z := by
      refine Q'.eqv_trans _
        (lowerSixRightDeltaPositive x t z +
          lowerSixRightDeltaSquareCoeff x t * 0) _ ?_ ?_
      · exact Q'.add_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hzero)
      · exact Q'.eqv_trans _ _ _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.mul_zero_eqv _))
          (Q'.eqv_of_eq (Q'.add_zero' _))
    exact Q'.le_trans' _ _ _ hpos
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _
        (Q'.eqv_symm hright) (Q'.eqv_symm hid)))
  exact Q'.le_of_sub_nonneg hdelta

#print axioms lowerSixRightRawSlack_delta_identity
#print axioms lowerSixRightDeltaSquareCoeff_nonnegative
#print axioms lowerSixRightDeltaPositive_nonnegative
#print axioms lowerSixRightRawSlack_monotone_step

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
