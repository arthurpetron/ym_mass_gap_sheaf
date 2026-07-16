/-
# Positive slope clearing of the lower-six local tail inequality

After the common Gaussian weight has been removed, the only non-polynomial
denominator in the remainder bracket is `(n+1)^2`.  The existing slope normal
form identifies that positive multiple exactly with a polynomial in the old
and next adjacent-root slopes.  This file clears it constructively and proves
an iff with the weight-free production inequality.
-/

import YMGap.Continuum.HarmonicLowerSixTailCorridor

namespace YMGap.Continuum.HarmonicLowerSixTailSlopeReduction

set_option maxHeartbeats 5000000
set_option maxRecDepth 20000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.HarmonicCutoffBoundary
open YMGap.Continuum.HarmonicLowerSixJointEndpointPayment
open YMGap.Continuum.HarmonicLowerSixSecondFluxSign
open YMGap.Continuum.HarmonicLowerSixTailLocalWeightReduction
open YMGap.Continuum.HarmonicLowerSixTailPaymentAssembly
open YMGap.Continuum.HarmonicMassCrossLowerSixInteriorAbel
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFlux
open YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier
open YMGap.Continuum.HarmonicMovingDeterminantThetaWindow
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Slope-polynomial form after clearing the positive `(n+1)^2` factor. -/
def LowerSixTailSecondFluxSlopeClearedBound (k n : Nat) : Prop :=
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let slopePoly := lowerSixHermiteRemainderSlopePolynomial k n
    (thetaRootSlope k n) (thetaRootSlope (k + 1) n)
  lowerSixJointSecondClearingScale k *
      -(Q'.ofNat 4 * slopePoly) ≤
    (A * A) *
      ((step * lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
        -lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
        (Q'.ofNat 15630 * RingNormaliser.qpow D 4))

private abbrev PE := RingNormaliser.PolyExpr

private def pSlopeClearLeftL : PE :=
  .mul (.mul (.var 0) (.var 0))
    (.mul (.var 1) (.neg (.mul (.const 4) (.var 2))))

private def pSlopeClearLeftR : PE :=
  .mul (.var 1)
    (.neg (.mul (.const 4)
      (.mul (.mul (.var 0) (.var 0)) (.var 2))))

private theorem pSlopeClearLeft_normal :
    RingNormaliser.normalize pSlopeClearLeftL =
      RingNormaliser.normalize pSlopeClearLeftR := by
  decide

private theorem slope_clear_left_algebra (A T B : Q') :
    (A * A) * (T * -(Q'.ofNat 4 * B)) ≈
      T * -(Q'.ofNat 4 * ((A * A) * B)) := by
  simpa [pSlopeClearLeftL, pSlopeClearLeftR, RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSlopeClearLeftL pSlopeClearLeftR pSlopeClearLeft_normal
      (fun | 0 => A | 1 => T | _ => B))

/-- Exact replacement of the cleared remainder bracket by its adjacent-slope
polynomial. -/
theorem lowerSixTailSecondFluxWeightFreeLeft_scaled_eqv_slopeLeft
    (k n : Nat) :
    let A := Q'.ofNat (n + 1)
    let weightFreeLeft := lowerSixJointSecondClearingScale k *
      -(Q'.ofNat 4 * lowerSixHermiteRemainderNetBracket k n)
    let slopeLeft := lowerSixJointSecondClearingScale k *
      -(Q'.ofNat 4 *
        lowerSixHermiteRemainderSlopePolynomial k n
          (thetaRootSlope k n) (thetaRootSlope (k + 1) n))
    (A * A) * weightFreeLeft ≈ slopeLeft := by
  let A := Q'.ofNat (n + 1)
  let T := lowerSixJointSecondClearingScale k
  let B := lowerSixHermiteRemainderNetBracket k n
  let P := lowerSixHermiteRemainderSlopePolynomial k n
    (thetaRootSlope k n) (thetaRootSlope (k + 1) n)
  have hpoly : (A * A) * B ≈ P := by
    dsimp only [A, B, P]
    exact lowerSixHermiteRemainderNetBracket_slopePolynomial k n
  have halgebra := slope_clear_left_algebra A T B
  have hreplace :
      T * -(Q'.ofNat 4 * ((A * A) * B)) ≈
        T * -(Q'.ofNat 4 * P) :=
    Q'.mul_eqv_congr_left _ _ _
      (Q'.neg_eqv_congr _ _
        (Q'.mul_eqv_congr_left _ _ _ hpoly))
  dsimp only [A, T, B, P] at halgebra hreplace ⊢
  exact Q'.eqv_trans _ _ _ halgebra hreplace

/-- Clearing `(n+1)^2` is an exact constructive equivalence, since that
factor is strictly positive. -/
theorem lowerSixTailSecondFluxWeightFree_iff_slopeCleared (k n : Nat) :
    LowerSixTailSecondFluxWeightFreeBound k n ↔
      LowerSixTailSecondFluxSlopeClearedBound k n := by
  let D := Q'.ofNat (k + 2)
  let A := Q'.ofNat (n + 1)
  let step := qpow (harmW k * harmW k) (2 * n + 1)
  let L := lowerSixJointSecondClearingScale k *
    -(Q'.ofNat 4 * lowerSixHermiteRemainderNetBracket k n)
  let R :=
    (step * lowerSixHermiteSecondFluxPoly D (Q'.ofNat (n + 1)) +
      -lowerSixHermiteSecondFluxPoly D (Q'.ofNat n)) +
      (Q'.ofNat 15630 * RingNormaliser.qpow D 4)
  let LC := lowerSixJointSecondClearingScale k *
    -(Q'.ofNat 4 *
      lowerSixHermiteRemainderSlopePolynomial k n
        (thetaRootSlope k n) (thetaRootSlope (k + 1) n))
  have hleft : (A * A) * L ≈ LC := by
    dsimp only [A, L, LC]
    exact lowerSixTailSecondFluxWeightFreeLeft_scaled_eqv_slopeLeft k n
  have hApos : (0 : Q') < A := by
    dsimp only [A]
    exact Q'.ofNat_succ_pos n
  have hAApos : (0 : Q') < A * A := Q'.mul_pos hApos hApos
  constructor
  · intro hweightFree
    unfold LowerSixTailSecondFluxWeightFreeBound at hweightFree
    dsimp only [D, A, step, L, R] at hweightFree
    have hscaled : (A * A) * L ≤ (A * A) * R :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hweightFree
        (Q'.le_of_lt hAApos)
    have hcleared : LC ≤ (A * A) * R :=
      Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft) hscaled
    unfold LowerSixTailSecondFluxSlopeClearedBound
    dsimp only [D, A, step, R, LC] at hcleared ⊢
    exact hcleared
  · intro hcleared
    unfold LowerSixTailSecondFluxSlopeClearedBound at hcleared
    dsimp only [D, A, step, R, LC] at hcleared
    have hscaled : (A * A) * L ≤ (A * A) * R :=
      Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hcleared
    have hweightFree : L ≤ R :=
      Q'.le_of_mul_le_mul_left hscaled hAApos
    unfold LowerSixTailSecondFluxWeightFreeBound
    dsimp only [D, A, step, L, R] at hweightFree ⊢
    exact hweightFree

theorem lowerSixTailSecondFluxLocalBound_iff_slopeCleared (k n : Nat) :
    LowerSixTailSecondFluxLocalBound k n ↔
      LowerSixTailSecondFluxSlopeClearedBound k n :=
  Iff.trans
    (lowerSixTailSecondFluxLocalBound_iff_weightFree k n)
    (lowerSixTailSecondFluxWeightFree_iff_slopeCleared k n)

#print axioms lowerSixTailSecondFluxWeightFreeLeft_scaled_eqv_slopeLeft
#print axioms lowerSixTailSecondFluxWeightFree_iff_slopeCleared
#print axioms lowerSixTailSecondFluxLocalBound_iff_slopeCleared

end YMGap.Continuum.HarmonicLowerSixTailSlopeReduction
