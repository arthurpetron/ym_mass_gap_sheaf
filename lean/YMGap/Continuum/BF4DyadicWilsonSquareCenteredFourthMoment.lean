/-
# Perimeter-independent fourth moment for the original centered Wilson square

The literal fundamental loop has a square cap of four, independent of its
perimeter.  The mean used below is computed from the SAME original odd
marginal.  A Type-level square certificate therefore caps its centered
character square by sixteen under every supported Haar insertion.  In
particular the raw projected source has a fourth-to-second Haar moment bound.
This does not replace the interacting `q*Pq` law by `q²`, or control the
remaining signed energy/variance error along a physical scaling family.
-/

import YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry
import YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram
import YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
import YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
import YMGap.Continuum.QuaternionHaarIntervalSecondMoment

namespace YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (sourceCharacter)
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquareChannelGeometry (paddedSquareSquareBound)
open YMGap.Continuum.BF4ExactSlabFixedSpatialActualMarginalDual
  (marginalWeight marginalCertificate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFamilyVarianceWard
  (marginalMass_positive)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSourceVarianceGram (oddCentered)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarDensityVariance
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.QuaternionHaarPolynomialInterval
open YMGap.Continuum.QuaternionHaarIntervalSecondMoment

local infix:50 " ≈ " => Q'.eqv
local notation:max "N" width:arg => List.length (baseLinks width)
local notation:max "H" blocks:arg => quaternionHaar blocks

/-- The center of the literal loop is bounded under its SAME original odd
marginal.  No edge/source measure substitution is used. -/
theorem paddedSquare_mean_square_le_four {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
    let W := marginalWeight w K width depth
    let m := normalizedMoment (N width) W f
      (marginalMass_positive hw0 hw1 K width hK depth)
    m*m ≤ (4 : Q') := by
  dsimp only
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let W := marginalWeight w K width depth
  let hz := marginalMass_positive hw0 hw1 K width hK depth
  let C := marginalCertificate hw0 hw1 K width hK depth
  have hf := (paddedSquareSquareBound scale width hwidth).support
  have hsecond := Interval.normalized_square_le
    (paddedSquareSquareBound scale width hwidth) C hz
  have hvariance := normalizedVariance_nonnegative C hz hf
  exact Q'.le_trans' _ _ _ (Q'.le_of_sub_nonneg hvariance) hsecond

/-- A witness-bearing cap for the ORIGINAL centered fundamental loop, uniform
in its perimeter.  The cap is on the ordinary Haar carrier under arbitrary
supported square insertions; it asserts no `q²=q*Pq` identity. -/
def paddedSquare_centered_squareBound {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) :
    SquareBound (N width)
      (oddCentered hw0 hw1 K width hK depth
        (sourceCharacter width (paddedSquare scale width hwidth).edges 1)) 16 := by
  let f := sourceCharacter width (paddedSquare scale width hwidth).edges 1
  let W := marginalWeight w K width depth
  let m := normalizedMoment (N width) W f
    (marginalMass_positive hw0 hw1 K width hK depth)
  have hm : m*m ≤ (4 : Q') :=
    paddedSquare_mean_square_le_four hw0 hw1 K width hK depth scale hwidth
  have hdelta : (0 : Q') ≤ 4 - m*m := Q'.sub_nonneg_of_le hm
  have hneg : (-m)*(-m) ≈ m*m :=
    poly_identity_of_normal_eq
      (.mul (.neg (.var 0)) (.neg (.var 0)))
      (.mul (.var 0) (.var 0)) (by decide) (fun _ => m)
  have hadd : m*m + (4 - m*m) ≈ (4 : Q') :=
    poly_identity_of_normal_eq
      (.add (.var 0) (.add (.const 4) (.neg (.var 0))))
      (.const 4) (by decide) (fun _ => m*m)
  have hf : SquareBound (N width) (polySmul 1 f) 4 :=
    SquareBound.changeCap (by decide : ((1 : Q')*1)*4 ≈ 4)
      ((paddedSquareSquareBound scale width hwidth).smul 1)
  have hmean : SquareBound (N width) (polySmul (-m) polyOne) 4 :=
    SquareBound.changeCap hadd
      ((SquareBound.changeCap hneg (SquareBound.constant (N width) (-m))).raise
        (4 - m*m) hdelta)
  change SquareBound (N width)
    (polyAdd (polySmul 1 f) (polySmul (-m) polyOne)) 16
  exact SquareBound.changeCap
    (by decide : sumBound (4 : Q') 4 ≈ 16) (hf.add hmean)

/-- The raw fourth moment is bounded by the raw second moment with the
perimeter-independent factor sixteen, for EVERY supported source `q`.  The
original odd center, cutoff, and one-slice carrier are unchanged. -/
theorem paddedSquare_centered_fourth_le_sixteen_second {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K width : Nat) (hK : headCutoff w ≤ K) (depth scale : Nat)
    (hwidth : side scale < width) (q : RatPoly)
    (hq : SupportedQuaternionBlocks (N width) q) :
    let psi := oddCentered hw0 hw1 K width hK depth
      (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
    H (N width) (polyMul (polyMul q (polyMul psi psi))
        (polyMul q (polyMul psi psi))) ≤
      16 * H (N width) (polyMul (polyMul q psi) (polyMul q psi)) := by
  dsimp only
  let psi := oddCentered hw0 hw1 K width hK depth
    (sourceCharacter width (paddedSquare scale width hwidth).edges 1)
  let a := polyMul q psi
  let b := polyMul q (polyMul psi psi)
  let P := paddedSquare_centered_squareBound hw0 hw1 K width hK depth scale hwidth
  have ha : SupportedQuaternionBlocks (N width) a := supported_polyMul hq P.support
  let I : Interval (N width) (polyMul psi psi) 16 :=
    ⟨supported_polyMul P.support P.support, P.nonnegative, P.certificate,
      (Certificate.constant (N width) 16 P.nonnegative).add
        (Certificate.square psi P.support)⟩
  have hbound := I.weighted_haar_bound (Certificate.square a ha)
  have hrecode : RatPolyCoeffEqv (polyMul b b)
      (polyMul (polyMul a a) (polyMul psi psi)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.mul (.var 1) (.var 1)))
        (.mul (.var 0) (.mul (.var 1) (.var 1))))
      (.mul (.mul (.mul (.var 0) (.var 1)) (.mul (.var 0) (.var 1)))
        (.mul (.var 1) (.var 1)))
      (by decide) (fun | 0 => q | _ => psi)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (haar_of_coeff hrecode))
    (Q'.le_trans' _ _ _ (Q'.le_abs_self _) hbound)

end YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment

#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment.paddedSquare_mean_square_le_four
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment.paddedSquare_centered_squareBound
#print axioms YMGap.Continuum.BF4DyadicWilsonSquareCenteredFourthMoment.paddedSquare_centered_fourth_le_sixteen_second
