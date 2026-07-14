/-
An exact shape certificate for positivity of the lower-six cleared slack.

At the first right-suffix mode the two elementary inequalities

  3D <= N^2,              5(2N+1) <= 3D

are enough.  After multiplication by 225, the cleared slack has an exact
four-term nonnegative decomposition.  This avoids approximate roots and
keeps the endpoint argument entirely in the constructive rational substrate.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotoneRational

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

def lowerSixShapeZ (D N : Q') : Q' :=
  RingNormaliser.qpow N 2 + -(Q'.ofNat 3 * D)

def lowerSixShapeV (D N : Q') : Q' :=
  Q'.ofNat 3 * D +
    -(Q'.ofNat 5 * (Q'.ofNat 2 * N + 1))

/-- Manifestly nonnegative decomposition of 225 times the raw slack. -/
def lowerSixShapePositive (D N : Q') : Q' :=
  let A := lowerSixRightRawNum D N
  let B := lowerSixRightRawDen D N
  let N2 := RingNormaliser.qpow N 2
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let z := lowerSixShapeZ D N
  let v := lowerSixShapeV D N
  Q'.ofNat 100 * D3 * (z + Q'.ofNat 3 * N) *
      (Q'.ofNat 3 * A + Q'.ofNat 5 * N2) +
    Q'.ofNat 4 * N2 * D3 * (N2 + Q'.ofNat 624 * z) +
    Q'.ofNat 117 * N2 * D2 * v *
      (Q'.ofNat 8 * D + Q'.ofNat 5 * B) +
    Q'.ofNat 225 * N2 * RingNormaliser.qpow B 2 *
      (D2 + -1)

private abbrev PE := RingNormaliser.PolyExpr

private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

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

private def pShapeZ (D N : PE) : PE :=
  padd (ppow N 2) (pneg (pmul (pc 3) D))

private def pShapeV (D N : PE) : PE :=
  padd (pmul (pc 3) D)
    (pneg (pmul (pc 5) (padd (pmul (pc 2) N) (pc 1))))

private def pShapePositive (D N : PE) : PE :=
  let A := pRawNum D N
  let B := pRawDen D N
  let N2 := ppow N 2
  let D2 := ppow D 2
  let D3 := ppow D 3
  let z := pShapeZ D N
  let v := pShapeV D N
  padd
    (padd
      (padd
        (pmul (pmul (pmul (pc 100) D3)
          (padd z (pmul (pc 3) N)))
          (padd (pmul (pc 3) A) (pmul (pc 5) N2)))
        (pmul (pmul (pmul (pc 4) N2) D3)
          (padd N2 (pmul (pc 624) z))))
      (pmul (pmul (pmul (pmul (pc 117) N2) D2) v)
        (padd (pmul (pc 8) D) (pmul (pc 5) B))))
    (pmul (pmul (pmul (pc 225) N2) (ppow B 2))
      (padd D2 (pneg (pc 1))))

private def pScaledSlackL : PE :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  pmul (pc 225) (pRawSlack D N)

private def pScaledSlackR : PE :=
  pShapePositive (RingNormaliser.PolyExpr.var 0)
    (RingNormaliser.PolyExpr.var 1)

private theorem pScaledSlack_normal :
    RingNormaliser.normalize pScaledSlackL =
      RingNormaliser.normalize pScaledSlackR := by decide

private def pFactorL : PE :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  padd (pmul (pc 3) (pRawNum D N)) (pmul (pc 5) (ppow N 2))

private def pFactorR : PE :=
  let D := RingNormaliser.PolyExpr.var 0
  let N := RingNormaliser.PolyExpr.var 1
  padd (padd (pmul (pc 10) (ppow N 2)) (pmul (pc 3) N))
    (pShapeZ D N)

private theorem pFactor_normal :
    RingNormaliser.normalize pFactorL =
      RingNormaliser.normalize pFactorR := by decide

theorem lowerSixRightRawSlack_scaled_shape_identity (D N : Q') :
    Q'.ofNat 225 * lowerSixRightRawSlack D N ≈
      lowerSixShapePositive D N := by
  simpa [pScaledSlackL, pScaledSlackR, pShapePositive,
    pShapeZ, pShapeV, pRawSlack, pRawNum, pRawDen,
    pc, padd, pmul, pneg, ppow,
    lowerSixShapePositive, lowerSixShapeZ, lowerSixShapeV,
    lowerSixRightRawSlack, lowerSixRightRawNum, lowerSixRightRawDen,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pScaledSlackL pScaledSlackR pScaledSlack_normal
      (fun | 0 => D | 1 => N | _ => (0 : Q')))

theorem lowerSixShapeLargeFactor_eqv (D N : Q') :
    Q'.ofNat 3 * lowerSixRightRawNum D N +
        Q'.ofNat 5 * RingNormaliser.qpow N 2 ≈
      (Q'.ofNat 10 * RingNormaliser.qpow N 2 + Q'.ofNat 3 * N) +
        lowerSixShapeZ D N := by
  simpa [pFactorL, pFactorR, pShapeZ, pRawNum, pRawDen,
    pc, padd, pmul, pneg, ppow,
    lowerSixShapeZ, lowerSixRightRawNum, lowerSixRightRawDen,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFactorL pFactorR pFactor_normal
      (fun | 0 => D | 1 => N | _ => (0 : Q')))

private theorem qpow_two_eqv_mul (a : Q') :
    RingNormaliser.qpow a 2 ≈ a * a := by
  change ((1 : Q') * a) * a ≈ a * a
  exact Q'.mul_eqv_congr_right _ _ a (Q'.one_mul_eqv a)

private theorem lowerSixShapePositive_nonnegative
    {D N : Q'}
    (hD1 : (1 : Q') ≤ D)
    (hN0 : (0 : Q') ≤ N)
    (hsq : Q'.ofNat 3 * D ≤ RingNormaliser.qpow N 2)
    (hshape : Q'.ofNat 5 * (Q'.ofNat 2 * N + 1) ≤
      Q'.ofNat 3 * D) :
    (0 : Q') ≤ lowerSixShapePositive D N := by
  let A := lowerSixRightRawNum D N
  let B := lowerSixRightRawDen D N
  let N2 := RingNormaliser.qpow N 2
  let D2 := RingNormaliser.qpow D 2
  let D3 := RingNormaliser.qpow D 3
  let z := lowerSixShapeZ D N
  let v := lowerSixShapeV D N
  have hD0 : (0 : Q') ≤ D := Q'.le_trans' _ _ _ (by decide) hD1
  have hN2 : (0 : Q') ≤ N2 := qpow_nonneg N hN0 2
  have hD2 : (0 : Q') ≤ D2 := qpow_nonneg D hD0 2
  have hD3 : (0 : Q') ≤ D3 := qpow_nonneg D hD0 3
  have hz : (0 : Q') ≤ z := Q'.sub_nonneg_of_le hsq
  have hv : (0 : Q') ≤ v := Q'.sub_nonneg_of_le hshape
  have hB : (0 : Q') ≤ B := by
    dsimp only [B]
    unfold lowerSixRightRawDen
    exact Q'.zero_le_add _ _ hD0
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hN0) (by decide))
  have hB2 : (0 : Q') ≤ RingNormaliser.qpow B 2 :=
    qpow_nonneg B hB 2
  have hD2one : (1 : Q') ≤ D2 := by
    have hmul := Q'.mul_le_mul_of_nonneg hD1 hD1 hD0 (by decide)
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv 1))
      (Q'.le_trans' _ _ _ hmul
        (Q'.le_of_eqv (Q'.eqv_symm (qpow_two_eqv_mul D))))
  have hu : (0 : Q') ≤ D2 + -1 := Q'.sub_nonneg_of_le hD2one
  have hsmall : (0 : Q') ≤ z + Q'.ofNat 3 * N :=
    Q'.zero_le_add _ _ hz (Q'.mul_nonneg _ _ (by decide) hN0)
  have hlargeR : (0 : Q') ≤
      (Q'.ofNat 10 * N2 + Q'.ofNat 3 * N) + z :=
    Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _ (by decide) hN2)
        (Q'.mul_nonneg _ _ (by decide) hN0)) hz
  have hlarge : (0 : Q') ≤ Q'.ofNat 3 * A + Q'.ofNat 5 * N2 :=
    Q'.le_trans' _ _ _ hlargeR
      (Q'.le_of_eqv (Q'.eqv_symm (lowerSixShapeLargeFactor_eqv D N)))
  have hsecondLast : (0 : Q') ≤ N2 + Q'.ofNat 624 * z :=
    Q'.zero_le_add _ _ hN2 (Q'.mul_nonneg _ _ (by decide) hz)
  have hrightLast : (0 : Q') ≤ Q'.ofNat 8 * D + Q'.ofNat 5 * B :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (by decide) hD0)
      (Q'.mul_nonneg _ _ (by decide) hB)
  unfold lowerSixShapePositive
  dsimp only [A, B, N2, D2, D3, z, v]
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.zero_le_add _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) hD3) hsmall) hlarge)
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) hN2) hD3) hsecondLast))
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (Q'.mul_nonneg _ _ (by decide) hN2) hD2) hv) hrightLast))
    (Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _ (by decide) hN2) hB2) hu)

/-- Shape inequalities sufficient for nonnegativity of the cleared raw
right-cell slack. -/
theorem lowerSixRightRawSlack_nonnegative_of_shape
    {D N : Q'}
    (hD1 : (1 : Q') ≤ D)
    (hN0 : (0 : Q') ≤ N)
    (hsq : Q'.ofNat 3 * D ≤ RingNormaliser.qpow N 2)
    (hshape : Q'.ofNat 5 * (Q'.ofNat 2 * N + 1) ≤
      Q'.ofNat 3 * D) :
    (0 : Q') ≤ lowerSixRightRawSlack D N := by
  have hpos := lowerSixShapePositive_nonnegative hD1 hN0 hsq hshape
  have hid := lowerSixRightRawSlack_scaled_shape_identity D N
  have hscaled : (0 : Q') ≤
      Q'.ofNat 225 * lowerSixRightRawSlack D N :=
    Q'.le_trans' _ _ _ hpos (Q'.le_of_eqv (Q'.eqv_symm hid))
  have hmul : Q'.ofNat 225 * (0 : Q') ≤
      Q'.ofNat 225 * lowerSixRightRawSlack D N :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_zero_eqv (Q'.ofNat 225))) hscaled
  exact FusionQuotientCollapse.le_of_mul_le_mul_left_pos
    (by decide : (0 : Q') < Q'.ofNat 225) hmul

#print axioms lowerSixRightRawSlack_scaled_shape_identity
#print axioms lowerSixShapeLargeFactor_eqv
#print axioms lowerSixRightRawSlack_nonnegative_of_shape

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixShapeCertificate
