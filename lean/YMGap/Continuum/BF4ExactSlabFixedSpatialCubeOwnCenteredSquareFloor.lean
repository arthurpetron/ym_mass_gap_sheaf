/-
# Positive ORIGINAL OWN-centered square from the computed face projection

The center is the constructed original depth-zero odd mean. Its proven
upper cap 1/4 leaves at least alpha/4 in the exact tested channel, and
the original centered-square projection theorem supplies a quantitative
positive floor. This finite cutoff-one width-two result does not establish
gain positivity, a late-cutoff statement, or changing-family survival.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall
import YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferStep (transferStep)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeTransfer (bentObservable)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnMeanSmall
  (originalOddMean originalOddMean_bounds meanCap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeSmallFundamentalCap
  (alphaCap deltaCap cubeFundamentalDelta_le_cap)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCubeCenteredSquareProjection
  (centeredBentMessage centeredSquare_channel_lower)
open YMGap.Continuum.BondMovingStep (coeffW)
open YMGap.Continuum.RingNormaliser (qpow poly_identity_of_normal_eq)

local notation "half" => HalfPow.half
local notation "eighth" => Q'.mkPos 1 8 (by decide)
local notation "sixteenth" => Q'.mkPos 1 16 (by decide)
local infix:50 " ≈ " => Q'.eqv
attribute [local irreducible] originalOddMean centeredBentMessage transferStep weightedMass
  baseLinks bentObservable

private theorem power_pos {w : Q'} (hw : (0 : Q') < w) : ∀ k, (0 : Q') < qpow w k
  | 0 => by change (0 : Q') < 1; decide
  | k+1 => Q'.mul_pos (power_pos hw k) hw

private theorem coefficient_pos {w : Q'} (hw : (0 : Q') < w) : (0 : Q') < coeffW w 1 := by
  change (0 : Q') < 2 * qpow w 3
  exact Q'.mul_pos (by decide) (power_pos hw 3)

private theorem power_nonneg (a : Q') (ha : (0 : Q') ≤ a) : ∀ k, (0 : Q') ≤ qpow a k
  | 0 => by change (0 : Q') ≤ 1; decide
  | k+1 => Q'.mul_nonneg _ _ (power_nonneg a ha k) ha

private theorem channel_factorization (a c : Q') :
    a*half + qpow a 5*eighth - c*(a+qpow a 5*sixteenth) ≈
      a*(half-c)+qpow a 5*(eighth-c*sixteenth) :=
  poly_identity_of_normal_eq
    (.add (.add (.mul (.var 0) (.var 3)) (.mul (.var 2) (.var 4)))
      (.neg (.mul (.var 1) (.add (.var 0) (.mul (.var 2) (.var 5))))))
    (.add (.mul (.var 0) (.add (.var 3) (.neg (.var 1))))
      (.mul (.var 2) (.add (.var 4) (.neg (.mul (.var 1) (.var 5))))))
    (by decide) (fun
      | 0 => a
      | 1 => c
      | 2 => qpow a 5
      | 3 => half
      | 4 => eighth
      | _ => sixteenth)

private theorem channel_core_lower (a c : Q') (ha : (0 : Q') ≤ a) (hc : c ≤ meanCap) :
    a*meanCap ≤ a*half + qpow a 5*eighth - c*(a+qpow a 5*sixteenth) := by
  have hgap : meanCap ≤ half-c :=
    Q'.le_trans' _ _ _ (by decide : meanCap ≤ half-meanCap)
      (Q'.add_le_add_left half _ _ (Q'.neg_le_neg hc))
  have hc16 : c*sixteenth ≤ eighth :=
    Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ sixteenth hc (by decide)) (by decide)
  have htail : (0 : Q') ≤ qpow a 5*(eighth-c*sixteenth) :=
    Q'.mul_nonneg _ _ (power_nonneg a ha 5) (Q'.sub_nonneg_of_le hc16)
  have hsum := Q'.add_le_add (Q'.mul_le_mul_of_nonneg_left _ _ a hgap ha) htail
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_of_eq (Q'.add_zero' (a*meanCap)).symm))
    (Q'.le_trans' _ _ _ hsum (Q'.ge_of_eqv (channel_factorization a c)))

/-- The tested channel at the actual original odd mean retains alpha/4. -/
theorem originalOddMean_channel_lower (w : Q') (hw : (0 : Q') < w)
    (ha : (0 : Q') ≤ coeffW w 1) (hα : coeffW w 1 ≤ alphaCap) :
    qpow w 12 * (coeffW w 1 * meanCap) ≤
      qpow w 12 * ((coeffW w 1 * half + qpow (coeffW w 1) 5*eighth) -
        originalOddMean w ha hα * (coeffW w 1 + qpow (coeffW w 1) 5*sixteenth)) :=
  Q'.mul_le_mul_of_nonneg_left _ _ (qpow w 12)
    (channel_core_lower _ _ ha (originalOddMean_bounds w ha hα).2)
    (Q'.le_of_lt (power_pos hw 12))

/-- Quantitative original C2 floor with its OWN odd mean and literal TF-c*T1. -/
theorem originalOwnCenteredSquare_lower (w : Q') (hw : (0 : Q') < w)
    (ha : (0 : Q') ≤ coeffW w 1) (hα : coeffW w 1 ≤ alphaCap) :
    let z := qpow w 12 * (coeffW w 1 * meanCap)
    half*(z*z) ≤ weightedMass w 1 2
      (polyMul (centeredBentMessage w (originalOddMean w ha hα))
        (centeredBentMessage w (originalOddMean w ha hα))) := by
  dsimp only
  let z := qpow w 12 * (coeffW w 1 * meanCap)
  let d := qpow w 12 * ((coeffW w 1 * half + qpow (coeffW w 1) 5*eighth) -
    originalOddMean w ha hα * (coeffW w 1 + qpow (coeffW w 1) 5*sixteenth))
  have hz : (0 : Q') ≤ z := Q'.mul_nonneg _ _ (Q'.le_of_lt (power_pos hw 12))
    (Q'.mul_nonneg _ _ ha (by decide))
  have hzd : z ≤ d := originalOddMean_channel_lower w hw ha hα
  have hd : (0 : Q') ≤ d := Q'.le_trans' _ _ _ hz hzd
  have hsq : z*z ≤ d*d := Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ z hzd hz)
    (Q'.mul_le_mul_of_nonneg_right _ _ d hzd hd)
  have hdelta := Q'.le_trans' _ _ _ (cubeFundamentalDelta_le_cap w ha hα)
    (by decide : deltaCap ≤ half)
  exact Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ half hsq HalfPow.half_nonneg)
    (centeredSquare_channel_lower w (originalOddMean w ha hα) ha hdelta)

/-- Strict positivity of the original OWN-centered square; no gain sign follows. -/
theorem originalOwnCenteredSquare_positive (w : Q') (hw : (0 : Q') < w)
    (ha : (0 : Q') ≤ coeffW w 1) (hα : coeffW w 1 ≤ alphaCap) :
    (0 : Q') < weightedMass w 1 2
      (polyMul (centeredBentMessage w (originalOddMean w ha hα))
        (centeredBentMessage w (originalOddMean w ha hα))) := by
  have hz : (0 : Q') < qpow w 12 * (coeffW w 1 * meanCap) :=
    Q'.mul_pos (power_pos hw 12) (Q'.mul_pos (coefficient_pos hw) (by decide))
  exact HeatKernelRGStep.lt_of_lt_of_le
    (Q'.mul_pos (by decide : (0 : Q') < half) (Q'.mul_pos hz hz))
    (originalOwnCenteredSquare_lower w hw ha hα)

end YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor.originalOddMean_channel_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor.originalOwnCenteredSquare_lower
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialCubeOwnCenteredSquareFloor.originalOwnCenteredSquare_positive
