/-
# Actual OWN-centered original variance comparison

At K=headCutoff(w)+stage the original block variances at u and u+d
use the SAME depth-stage terminal source and the SAME stage odd-window
mean. The constructed terminal comparison and sharp Schur closure give
the upper normalized comparison with factor (1+comparisonEta)^2.

Only the two strictly positive ORIGINAL chronological partitions are
inverted. Signed sources, zero variance and d=0 are retained. This is a
finite upper comparison, not a lower survival bound, stationary-law pin,
changing-family uniform estimate or physical/continuum closure.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
import YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit

namespace YMGap.Continuum.BF4WilsonAllNomeOriginalVarianceComparison

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferSandwich (weightedMass)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalBracket
  (terminalMessage terminalPair_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialMiddlePairing (middleRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe
  (SourceLoop sourceCharacter sourceCharacter_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialBlockMultiplicationDefect (originalBlockTransfer)
open YMGap.Continuum.BF4ExactSlabFixedSpatialTerminalComparison (comparisonEta)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFilteredVarianceComparison
  (filtered_variance_cleared_le)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit (originalOwnBlockVariance)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.QuaternionHaarDensityVariance (shifted shifted_supported)
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier (polyMul)

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
attribute [local irreducible] baseLinks terminalMessage weightedMass sourceCharacter middleRatio

private theorem cleared_positive_partition_le (Zu Zt Bu Bt F : Q')
    (hu : (0 : Q') < Zu) (ht : (0 : Q') < Zt)
    (h : Zu*Bt ≤ F*(Zt*Bu)) :
    Bt*Q'.recipPos Zt ht ≤ F*(Bu*Q'.recipPos Zu hu) := by
  let ru := Q'.recipPos Zu hu
  let rt := Q'.recipPos Zt ht
  have hm := Q'.mul_le_mul_of_nonneg_left _ _ (ru*rt) h
    (Q'.mul_nonneg _ _ (Q'.le_of_lt (Q'.recipPos_pos Zu hu))
      (Q'.le_of_lt (Q'.recipPos_pos Zt ht)))
  have hleft : (ru*rt)*(Zu*Bt) ≈ Bt*rt :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.var 2) (.var 0)) (.mul (.var 3) (.var 1)))
      (by decide) (fun | 0 => ru | 1 => rt | 2 => Zu | _ => Bt))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Bt*rt) (Q'.mul_recipPos_eqv Zu hu))
        (Q'.one_mul_eqv (Bt*rt)))
  have hright : (ru*rt)*(F*(Zt*Bu)) ≈ F*(Bu*ru) :=
    Q'.eqv_trans _ _ _ (poly_identity_of_normal_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.mul (.var 3) (.var 4))))
      (.mul (.var 2) (.mul (.mul (.var 3) (.var 1)) (.mul (.var 4) (.var 0))))
      (by decide) (fun | 0 => ru | 1 => rt | 2 => F | 3 => Zt | _ => Bu))
      (Q'.mul_eqv_congr_left F _ _ (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_right _ _ (Bu*ru) (Q'.mul_recipPos_eqv Zt ht))
        (Q'.one_mul_eqv (Bu*ru))))
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
    (Q'.le_trans' _ _ _ hm (Q'.le_of_eqv hright))

/-- The existing original OWN block variances obey the constructed finite
upper comparison. The stage mean is identical at both block times. -/
theorem originalOwnBlockVariance_comparison {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < 1) (scale width : Nat)
    (hwidth : side scale < width) (stage u d : Nat) (hdepth : 1 ≤ stage+u) :
    originalOwnBlockVariance hw0 hw1 scale width hwidth stage (u+d) ≤
      ((1+comparisonEta hw0 hw1 width (stage+u-1))*
        (1+comparisonEta hw0 hw1 width (stage+u-1))) *
      originalOwnBlockVariance hw0 hw1 scale width hwidth stage u := by
  let K := headCutoff w+stage
  let square := paddedSquare scale width hwidth
  let f := sourceCharacter width (SourceLoop.edges square) 1
  let c := middleRatio hw0 hw1 K width (Nat.le_add_right _ _) (stage+1) stage f
  let psi := shifted f c
  let Au := terminalMessage w K width (stage+u)
  let At := terminalMessage w K width (stage+(u+d))
  let bu := originalBlockTransfer w K width u
    (polyMul (terminalMessage w K width stage) psi)
  let bt := originalBlockTransfer w K width (u+d)
    (polyMul (terminalMessage w K width stage) psi)
  let Zu := weightedMass w K width (polyMul Au Au)
  let Zt := weightedMass w K width (polyMul At At)
  let Bu := weightedMass w K width (polyMul bu bu)
  let Bt := weightedMass w K width (polyMul bt bt)
  let F := (1+comparisonEta hw0 hw1 width (stage+u-1))*
    (1+comparisonEta hw0 hw1 width (stage+u-1))
  have hp : SupportedQuaternionBlocks (N width) psi :=
    shifted_supported (sourceCharacter_supported width square.edges 1) c
  have hclear : Zu*Bt ≤ F*(Zt*Bu) := by
    simpa only [Zu, Zt, Bu, Bt, Au, At, bu, bt, F, Nat.add_assoc] using
      filtered_variance_cleared_le hw0 hw1 K width (Nat.le_add_right _ _)
        stage u d hdepth hp
  have hZu : (0 : Q') < Zu :=
    terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _)
      (stage+u) (stage+u)
  have hZt : (0 : Q') < Zt :=
    terminalPair_positive hw0 hw1 K width (Nat.le_add_right _ _)
      (stage+(u+d)) (stage+(u+d))
  have hnorm := cleared_positive_partition_le Zu Zt Bu Bt F hZu hZt hclear
  change Bt*Q'.recipPos Zt hZt ≤ F*(Bu*Q'.recipPos Zu hZu)
  exact hnorm

end YMGap.Continuum.BF4WilsonAllNomeOriginalVarianceComparison

#print axioms YMGap.Continuum.BF4WilsonAllNomeOriginalVarianceComparison.originalOwnBlockVariance_comparison
