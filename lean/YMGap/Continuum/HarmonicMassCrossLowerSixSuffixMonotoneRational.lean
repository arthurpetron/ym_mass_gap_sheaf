/-
Rational-coordinate wrapper for the lower-six suffix monotonicity engine.

The polynomial engine is naturally stated in translated coordinates
`D = 50 + x`, `N = 13 + t`, `N^2 = 3D + z`.  Here the translated
coordinates are chosen inside the constructive rational substrate itself:

  x = D - 50,  t = N - 13,  z = N^2 - 3D.

Reflective polynomial identities, rather than nonlinear `omega` reasoning,
certify the coordinate cancellations and transport the conclusion back to
the original variables.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone

namespace YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotoneRational

set_option maxHeartbeats 2400000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotone

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pc (n : Int) : PE := .const n
private def padd (a b : PE) : PE := .add a b
private def pmul (a b : PE) : PE := .mul a b
private def pneg (a : PE) : PE := .neg a
private def ppow (a : PE) (n : Nat) : PE := .pow a n

private def pD : PE := RingNormaliser.PolyExpr.var 0
private def pN : PE := RingNormaliser.PolyExpr.var 1
private def pX : PE := padd pD (pneg (pc 50))
private def pT : PE := padd pN (pneg (pc 13))
private def pDTranslated : PE := padd (pc 50) pX
private def pNTranslated : PE := padd (pc 13) pT
private def pZ : PE :=
  padd (ppow pN 2) (pneg (pmul (pc 3) pD))

private theorem pDTranslated_normal :
    RingNormaliser.normalize pDTranslated =
      RingNormaliser.normalize pD := by decide

private theorem pNTranslated_normal :
    RingNormaliser.normalize pNTranslated =
      RingNormaliser.normalize pN := by decide

private theorem pSquareSlack_normal :
    RingNormaliser.normalize (ppow pNTranslated 2) =
      RingNormaliser.normalize
        (padd (pmul (pc 3) pDTranslated) pZ) := by decide

theorem lowerSixDTranslated_eqv (D : Q') :
    Q'.ofNat 50 + (D + -Q'.ofNat 50) ≈ D := by
  simpa [pDTranslated, pX, pD, pc, padd, pneg,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pDTranslated pD pDTranslated_normal
      (fun | 0 => D | _ => (0 : Q')))

theorem lowerSixNTranslated_eqv (N : Q') :
    Q'.ofNat 13 + (N + -Q'.ofNat 13) ≈ N := by
  simpa [pNTranslated, pT, pN, pc, padd, pneg,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pNTranslated pN pNTranslated_normal
      (fun | 1 => N | _ => (0 : Q')))

theorem lowerSixSquareSlack_eqv (D N : Q') :
    RingNormaliser.qpow (Q'.ofNat 13 + (N + -Q'.ofNat 13)) 2 ≈
      Q'.ofNat 3 * (Q'.ofNat 50 + (D + -Q'.ofNat 50)) +
        (RingNormaliser.qpow N 2 + -(Q'.ofNat 3 * D)) := by
  simpa [pSquareSlack_normal, pDTranslated, pNTranslated,
    pX, pT, pZ, pD, pN, pc, padd, pmul, pneg, ppow,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      (ppow pNTranslated 2)
      (padd (pmul (pc 3) pDTranslated) pZ)
      pSquareSlack_normal
      (fun | 0 => D | 1 => N | _ => (0 : Q')))

private theorem mul_eqv_congr' {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' := by
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

private theorem lowerSixRightRawDen_eqv_congr
    {D D' N N' : Q'} (hD : D ≈ D') (hN : N ≈ N') :
    lowerSixRightRawDen D N ≈ lowerSixRightRawDen D' N' := by
  unfold lowerSixRightRawDen
  exact Q'.add_eqv_congr' hD
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) N N' hN)
      (Q'.eqv_refl 1))

private theorem lowerSixRightRawNum_eqv_congr
    {D D' N N' : Q'} (hD : D ≈ D') (hN : N ≈ N') :
    lowerSixRightRawNum D N ≈ lowerSixRightRawNum D' N' := by
  have hden := lowerSixRightRawDen_eqv_congr hD hN
  unfold lowerSixRightRawNum
  exact Q'.add_eqv_congr'
    (mul_eqv_congr' hN hden)
    (Q'.neg_eqv_congr _ _
      (mul_eqv_congr'
        (Q'.add_eqv_congr' hN (Q'.eqv_refl 1)) hD))

private theorem lowerSixRightRawSlack_eqv_congr
    {D D' N N' : Q'} (hD : D ≈ D') (hN : N ≈ N') :
    lowerSixRightRawSlack D N ≈ lowerSixRightRawSlack D' N' := by
  have hden := lowerSixRightRawDen_eqv_congr hD hN
  have hnum := lowerSixRightRawNum_eqv_congr hD hN
  have hD2 := RingNormaliser.qpow_eqv_congr hD 2
  have hD3 := RingNormaliser.qpow_eqv_congr hD 3
  have hN2 := RingNormaliser.qpow_eqv_congr hN 2
  have hden2 := RingNormaliser.qpow_eqv_congr hden 2
  have hnum2 := RingNormaliser.qpow_eqv_congr hnum 2
  unfold lowerSixRightRawSlack
  exact Q'.add_eqv_congr'
    (mul_eqv_congr'
      (mul_eqv_congr' (Q'.eqv_refl (Q'.ofNat 4)) hnum2) hD3)
    (Q'.neg_eqv_congr _ _
      (mul_eqv_congr'
        (mul_eqv_congr'
          (Q'.add_eqv_congr'
            (mul_eqv_congr' (Q'.eqv_refl (Q'.ofNat 12)) hD2)
            (Q'.eqv_refl 1))
          hN2)
        hden2))

theorem lowerSixRightRawSlack_translated_eqv (D N : Q') :
    lowerSixRightRawSlack
        (Q'.ofNat 50 + (D + -Q'.ofNat 50))
        (Q'.ofNat 13 + (N + -Q'.ofNat 13)) ≈
      lowerSixRightRawSlack D N := by
  exact lowerSixRightRawSlack_eqv_congr
    (lowerSixDTranslated_eqv D) (lowerSixNTranslated_eqv N)

theorem lowerSixRightRawSlack_translated_succ_eqv (D N : Q') :
    lowerSixRightRawSlack
        (Q'.ofNat 50 + (D + -Q'.ofNat 50))
        ((Q'.ofNat 13 + (N + -Q'.ofNat 13)) + 1) ≈
      lowerSixRightRawSlack D (N + 1) := by
  exact lowerSixRightRawSlack_eqv_congr
    (lowerSixDTranslated_eqv D)
    (Q'.add_eqv_congr' (lowerSixNTranslated_eqv N) (Q'.eqv_refl 1))

/-- The cleared right-cell slack is forward-monotone directly in rational
variables once `D >= 50`, `N >= 13`, and `N^2 >= 3D`. -/
theorem lowerSixRightRawSlack_monotone_rational
    {D N : Q'}
    (hD : Q'.ofNat 50 ≤ D)
    (hN : Q'.ofNat 13 ≤ N)
    (hsq : Q'.ofNat 3 * D ≤ RingNormaliser.qpow N 2) :
    lowerSixRightRawSlack D N ≤
      lowerSixRightRawSlack D (N + 1) := by
  let x : Q' := D + -Q'.ofNat 50
  let t : Q' := N + -Q'.ofNat 13
  let z : Q' := RingNormaliser.qpow N 2 + -(Q'.ofNat 3 * D)
  have hx : (0 : Q') ≤ x := Q'.sub_nonneg_of_le hD
  have ht : (0 : Q') ≤ t := Q'.sub_nonneg_of_le hN
  have hz : (0 : Q') ≤ z := Q'.sub_nonneg_of_le hsq
  have hstep := lowerSixRightRawSlack_monotone_step hx ht hz
    (lowerSixSquareSlack_eqv D N)
  have hleft := lowerSixRightRawSlack_translated_eqv D N
  have hright := lowerSixRightRawSlack_translated_succ_eqv D N
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv hright))

#print axioms lowerSixDTranslated_eqv
#print axioms lowerSixNTranslated_eqv
#print axioms lowerSixSquareSlack_eqv
#print axioms lowerSixRightRawSlack_translated_eqv
#print axioms lowerSixRightRawSlack_translated_succ_eqv
#print axioms lowerSixRightRawSlack_monotone_rational

end YMGap.Continuum.HarmonicMassCrossLowerSixSuffixMonotoneRational
