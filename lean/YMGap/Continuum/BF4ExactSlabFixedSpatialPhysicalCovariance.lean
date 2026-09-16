/-
# Separation decay for the original reflected physical-time observations

Use a common chart H=R+n. The lower advanced observation has offsets R-d;
the reflected upper observation has offsets H+d. Thus the SAME finite
connected expectation has two windows separated by exactly n transitions.
The caps depend on the two original signed presentations, not their time
labels, the boundary depth, retained heat stage or physical lag.

This module applies the actual separated-window estimate without changing
the selected action or partition. Nome and spatial width dependence remain;
no continuum-uniform rate or physical Hamiltonian gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator
import YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
import YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser (poly_identity_of_normal_eq)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowProbeSpan (sourceSpan sourceSpan_supported)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowReflectionPositive (mirrorSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicSeminorm (PhysicalSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicUnit
open YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalTimeShift
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPairing (windowRatio)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabFixedSpatialReflectedSeparatedProbe
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabFixedSpatialUniformProbeCap
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
open YMGap.Continuum.BF4ExactSlabFixedSpatialOriginalConnectedCorrelator
open YMGap.Continuum.BF4ExactSlabFixedSpatialCenteredMoments
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

attribute [local irreducible] baseLinks windowRatio chartScalar

/-- The actual two-presentation coefficient envelope, with no physical lag. -/
def separationCap (width : Nat) (xs ys : DistanceSpan) : Q' :=
  (polynomialCap (sourceSpan width xs)+polynomialCap (sourceSpan width xs)) *
    (polynomialCap (sourceSpan width ys)+polynomialCap (sourceSpan width ys))

theorem separationCap_nonnegative (width : Nat) (xs ys : DistanceSpan) :
    (0 : Q') ≤ separationCap width xs ys :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (polynomialCap_nonnegative _) (polynomialCap_nonnegative _))
    (Q'.zero_le_add _ _ (polynomialCap_nonnegative _) (polynomialCap_nonnegative _))

private theorem sourceSpan_encode_cap (width R : Nat) (xs : DistanceSpan) :
    polynomialCap (sourceSpan width (encodeChart R xs)) = polynomialCap (sourceSpan width xs) := by
  apply polynomialCap_congr
  rw [coefficients_sourceSpan, coefficients_sourceSpan, eraseSpan_encodeChart]

private theorem support_mono {a b : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks a p) (hab : a ≤ b) : SupportedQuaternionBlocks b p :=
  fun t ht => Nat.le_trans (hp t ht) (Nat.mul_le_mul_left 4 hab)

private theorem source_supported (width H : Nat) (xs : DistanceSpan) (hx : radius xs ≤ H) :
    SupportedQuaternionBlocks ((H+1)*(N width)) (sourceSpan width xs) :=
  sourceSpan_supported width H xs
    (fun x hxmem e he => Nat.le_trans (radius_within xs x hxmem e he) hx)

private theorem upper_supported (width H : Nat) (xs : DistanceSpan) (hx : radius xs ≤ H) :
    SupportedQuaternionBlocks ((2*H+1)*(N width))
      (liftBoundary (H*(N width)) (sourceSpan width xs)) := by
  have h := lift_supported (source_supported width H xs hx) (H*(N width))
  have he : (H+1)*(N width)+H*(N width) = (2*H+1)*(N width) := by
    simp only [Nat.add_mul, Nat.one_mul, Nat.two_mul]
    omega
  rw [he] at h
  exact h

private theorem lower_supported (width R n : Nat) (ys : DistanceSpan) (hy : radius ys ≤ R) :
    SupportedQuaternionBlocks ((2*(R+n)+1)*(N width))
      (sourceSpan width (encodeChart R ys)) :=
  support_mono (sourceSpan_supported width R _ (encodeChart_within R ys hy))
    (Nat.mul_le_mul_right (N width) (by omega))

private theorem radius_time_le {width : Nat} (R n : Nat) (y : PhysicalSpan width)
    (hy : radius y.val ≤ R) : radius (physicalTime n y).val ≤ R+n :=
  Nat.le_trans (radius_advance_le n y.val) (Nat.add_le_add_right hy n)

/-- Exact original joint observation pin; the chart and both boundaries stay fixed. -/
theorem chart_joint_separated {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage R n : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) (t : Nat) :
    chartScalar hw0 hw1 width stage (R+n) x (physicalTime n y) t ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*(R+n)) t
        (polyMul (sourceSpan width (encodeChart R y.val))
          (liftBoundary ((R+n)*(N width)) (sourceSpan width x.val))) := by
  have hxH : radius x.val ≤ R+n := Nat.le_trans hx (Nat.le_add_right _ _)
  have hyH := radius_time_le R n y hy
  have hsource := mixedProduct_supported width (R+n) (encodeChart (R+n) x.val)
    (encodeChart (R+n) (physicalTime n y).val)
    (encodeChart_within (R+n) (physicalTime n y).val hyH)
  have htarget := supported_polyMul (lower_supported width R n y.val hy)
    (upper_supported width (R+n) x.val hxH)
  exact Q'.eqv_trans _ _ _ (chartScalar_pin hw0 hw1 width stage (R+n) x
    (physicalTime n y) hxH hyH t)
    (windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*(R+n)) t hsource htarget
      (mixedProduct_reflected_separated ((2*(R+n)+1)*(N width)) width R n x.val y.val hx))

/-- Left unit marginal is the lifted upper probe on the SAME original chart. -/
theorem chart_upper_marginal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage H : Nat) (x : PhysicalSpan width) (hx : radius x.val ≤ H) (t : Nat) :
    chartScalar hw0 hw1 width stage H x (unit width) t ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*H) t (liftBoundary (H*(N width)) (sourceSpan width x.val)) := by
  have hu : radius (unit width).val ≤ H := Nat.zero_le H
  have hsource := mixedProduct_supported width H (encodeChart H x.val)
    (encodeChart H (unit width).val) (encodeChart_within H (unit width).val hu)
  have he : PaddedPolynomialCoeffEqv ((2*H+1)*(N width))
      (mixedProduct width H (encodeChart H x.val) (encodeChart H (unit width).val))
      (liftBoundary (H*(N width)) (sourceSpan width x.val)) := by
    change PaddedPolynomialCoeffEqv _
      (mixedProduct width H (encodeChart H x.val) (encodeChart H unitSpan)) _
    rw [mixedProduct, encodeChart_unit, sourceSpan_unit, mirrorSpan_encodeChart H x.val hx]
    exact (PaddedPolynomialCoeffEqv.of_coeff (RatPolyCoeffEqv.mul_one _)).trans
      (sourceSpan_advance ((2*H+1)*(N width)) width H x.val)
  exact Q'.eqv_trans _ _ _ (chartScalar_pin hw0 hw1 width stage H x (unit width) hx hu t)
    (windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*H) t hsource (upper_supported width H x.val hx) he)

private theorem mirror_unit (H : Nat) : mirrorSpan H unitSpan = unitSpan := rfl

/-- Right unit marginal is the unshifted lower probe on the SAME original chart. -/
theorem chart_lower_marginal {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage R n : Nat) (y : PhysicalSpan width) (hy : radius y.val ≤ R) (t : Nat) :
    chartScalar hw0 hw1 width stage (R+n) (unit width) (physicalTime n y) t ≈
      windowRatio hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
        t (2*(R+n)) t (sourceSpan width (encodeChart R y.val)) := by
  have he : RatPolyCoeffEqv
      (mixedProduct width (R+n) (encodeChart (R+n) (unit width).val)
        (encodeChart (R+n) (physicalTime n y).val))
      (sourceSpan width (encodeChart R y.val)) := by
    change RatPolyCoeffEqv (mixedProduct width (R+n) (encodeChart (R+n) unitSpan)
      (encodeChart (R+n) (advanceSpan n y.val))) _
    rw [mixedProduct, encodeChart_unit, mirror_unit, sourceSpan_unit, encodeChart_advance]
    exact RatPolyCoeffEqv.one_mul _
  exact Q'.eqv_trans _ _ _ (chartScalar_pin hw0 hw1 width stage (R+n) (unit width)
    (physicalTime n y) (Nat.zero_le _) (radius_time_le R n y hy) t)
    (windowRatio_congr hw0 hw1 (headCutoff w+stage) width (Nat.le_add_right _ _)
      t (2*(R+n)) t he)

/-- The physical-lag estimate for the literal finite connected expectation.
Only the actual original action is used; t and n are independent parameters. -/
theorem connectedScalar_abs_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage R n : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) (t : Nat) :
    Q'.abs (connectedScalar hw0 hw1 width stage (R+n) x (physicalTime n y) t) ≤
      separationCap width x.val y.val * mixRate hw0 hw1 width ^ n := by
  have hj := chart_joint_separated hw0 hw1 width stage R n x y hx hy t
  have hl := chart_upper_marginal hw0 hw1 width stage (R+n) x
    (Nat.le_trans hx (Nat.le_add_right _ _)) t
  have hr := chart_lower_marginal hw0 hw1 width stage R n y hy t
  have hm := Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ hl)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ hr) (Q'.mul_comm_eqv _ _))
  have hb := polynomialWindow_covariance_bound hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) t R n (R+n) t
    (sourceSpan width (encodeChart R y.val)) (sourceSpan width x.val)
    (sourceSpan_supported width R _ (encodeChart_within R y.val hy))
    (source_supported width (R+n) x.val (Nat.le_trans hx (Nat.le_add_right _ _)))
  have hlen : R+n+(R+n) = 2*(R+n) := by omega
  rw [hlen, sourceSpan_encode_cap] at hb
  have hcap : (polynomialCap (sourceSpan width x.val)+polynomialCap (sourceSpan width x.val)) *
      (mixRate hw0 hw1 width ^ n *
        (polynomialCap (sourceSpan width y.val)+polynomialCap (sourceSpan width y.val))) ≈
      separationCap width x.val y.val * mixRate hw0 hw1 width ^ n :=
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 2) (.var 1))) (.mul (.mul (.var 0) (.var 1)) (.var 2))
      (by decide) (fun
        | 0 => polynomialCap (sourceSpan width x.val)+polynomialCap (sourceSpan width x.val)
        | 1 => polynomialCap (sourceSpan width y.val)+polynomialCap (sourceSpan width y.val)
        | _ => mixRate hw0 hw1 width ^ n)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.add_eqv_congr' hj (Q'.neg_eqv_congr _ _ hm))))
    (Q'.le_trans' _ _ _ hb (Q'.le_of_eqv hcap))

/-- The existing explicit-modulus connected limit inherits both bounds
directly on its own approximations. No cutoff/time limits are interchanged. -/
theorem connectedLimit_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage R n : Nat) (x y : PhysicalSpan width)
    (hx : radius x.val ≤ R) (hy : radius y.val ≤ R) :
    let Z := connectedLimit hw0 hw1 width stage (R+n) x (physicalTime n y)
      (Nat.le_trans hx (Nat.le_add_right _ _)) (radius_time_le R n y hy)
    let E := separationCap width x.val y.val * mixRate hw0 hw1 width ^ n
    leEv (ofQ' (-E)) Z ∧ leEv Z (ofQ' E) := by
  constructor
  · apply leEv_ofQ'_of_approx_ge
    intro k
    simp only [connectedLimit, ofQ'CauchySeq_approx]
    exact Q'.le_trans' _ _ _
      (Q'.neg_le_neg (connectedScalar_abs_le hw0 hw1 width stage R n x y hx hy _))
      (ExpNeg.neg_abs_le _)
  · apply leEv_le_ofQ'_of_approx_le
    intro k
    simp only [connectedLimit, ofQ'CauchySeq_approx]
    exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
      (connectedScalar_abs_le hw0 hw1 width stage R n x y hx hy _)

/-- Actual centered physical-time moments have a geometric envelope with
an explicitly computed, lag-independent presentation prefactor. -/
theorem centeredMoment_le {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width stage n : Nat) (x y : PhysicalSpan width) :
    leEv (centeredMoment hw0 hw1 width stage n x y)
      (ofQ' (separationCap width x.val y.val * mixRate hw0 hw1 width ^ n)) := by
  let R := max (radius x.val) (radius y.val)
  have hx : radius x.val ≤ R := Nat.le_max_left _ _
  have hy : radius y.val ≤ R := Nat.le_max_right _ _
  have hpin := (centeredMoment_pin hw0 hw1 width stage n x y).symm.trans
    (centeredTime_originalCorrelator hw0 hw1 width stage n (R+n) x y
      (Nat.le_trans hx (Nat.le_add_right _ _)) (radius_time_le R n y hy))
  exact leEv_trans (leEv_of_equiv (Quotient.exact hpin))
    (connectedLimit_bounds hw0 hw1 width stage R n x y hx hy).2

end YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance

#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.separationCap
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.separationCap_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.chart_joint_separated
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.chart_upper_marginal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.chart_lower_marginal
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.connectedScalar_abs_le
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.connectedLimit_bounds
#print axioms YMGap.Continuum.BF4ExactSlabFixedSpatialPhysicalCovariance.centeredMoment_le
