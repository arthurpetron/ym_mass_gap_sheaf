/-
# All-nome separated covariance for literal Wilson expressions

The reflected joint source and its two unit marginals are rewritten as two
fixed Wilson polynomials separated by the actual physical lag.  The existing
arbitrary-polynomial transfer covariance estimate then applies with the same
original action, cutoff, partition, width and nome.  Passing the finite bound
through the witnessed original joint limits gives decay of the literal-width
all-nome intrinsic centered pairing.

The prefactor depends on the two expressions and their common finite radius,
but not on the lag.  No small-nome, spatial-collar, completion, or continuum
claim is made.
-/

import YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
import YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence

namespace YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift source_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within unit chart_unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonSeparatedProbeControl
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
open YMGap.Continuum.BF4ExactSlabFixedSpatialSeparatedCovariance
open YMGap.Continuum.BF4ExactSlabFixedSpatialTransferMixingRate (mixRate)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeTimeForm
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
  (intrinsicForm_unit_invariant_right)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4CompactActionCPOrder (supported_polyMul)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.QuaternionHaarSupportedPolynomialInterval
  (polynomialCap polynomialCap_nonnegative)

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

/-- The lower source in the smallest common chart of the two expressions. -/
def lowerSource {width : Nat} (R : Nat) (y : IntrinsicExpression width) : RatPoly :=
  sourcePolynomial (chart R y)

/-- Reflection is removed from the upper source before its physical shift. -/
def upperSource {width : Nat} (x : IntrinsicExpression width) : RatPoly :=
  sourcePolynomial (reverse x)

/-- A lag-independent covariance prefactor for the two literal sources. -/
def separationCap {width : Nat} (x y : IntrinsicExpression width) : Q' :=
  let R := max x.radius y.radius
  (polynomialCap (upperSource x)+polynomialCap (upperSource x)) *
    (polynomialCap (lowerSource R y)+polynomialCap (lowerSource R y))

theorem separationCap_nonnegative {width : Nat} (x y : IntrinsicExpression width) :
    (0 : Q') ≤ separationCap x y :=
  Q'.mul_nonneg _ _
    (Q'.zero_le_add _ _ (polynomialCap_nonnegative _) (polynomialCap_nonnegative _))
    (Q'.zero_le_add _ _ (polynomialCap_nonnegative _) (polynomialCap_nonnegative _))

private theorem qmul {a b c d : Q'} (h : a ≈ b) (k : c ≈ d) : a*c ≈ b*d :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ h)
    (Q'.mul_eqv_congr_left _ _ _ k)

private theorem support_mono {small large : Nat} {p : RatPoly}
    (hp : SupportedQuaternionBlocks small p) (h : small ≤ large) :
    SupportedQuaternionBlocks large p :=
  fun term hm => Nat.le_trans (hp term hm) (Nat.mul_le_mul_left 4 h)

private theorem mixed_source_separated {width R n : Nat}
    (x y : IntrinsicExpression width) (hx : x.radius ≤ R) :
    PaddedPolynomialCoeffEqv ((2*(R+n)+1)*(N width))
      (sourcePolynomial
        (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))))
      (polyMul (lowerSource R y)
        (liftBoundary ((R+n)*(N width)) (upperSource x))) := by
  rw [mirror_chart_reverse (R+n) x (Nat.le_trans hx (Nat.le_add_right _ _)),
    chart_advance_add_center]
  change PaddedPolynomialCoeffEqv _
    (polyMul (sourcePolynomial (shift (R+n) (reverse x))) (lowerSource R y))
    (polyMul (lowerSource R y) (liftBoundary ((R+n)*(N width)) (upperSource x)))
  exact ((source_shift ((2*(R+n)+1)*(N width)) (R+n) (reverse x)).mul
    (.refl _ (lowerSource R y))).trans
      (.of_coeff (RatPolyCoeffEqv.mul_comm _ _))

private theorem left_source_separated {width R n : Nat}
    (x : IntrinsicExpression width) (hx : x.radius ≤ R) :
    PaddedPolynomialCoeffEqv ((2*(R+n)+1)*(N width))
      (sourcePolynomial
        (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width))))
      (liftBoundary ((R+n)*(N width)) (upperSource x)) := by
  rw [mirror_chart_reverse (R+n) x (Nat.le_trans hx (Nat.le_add_right _ _)), chart_unit]
  change PaddedPolynomialCoeffEqv _
    (polyMul (sourcePolynomial (shift (R+n) (reverse x))) polyOne) _
  exact ((source_shift ((2*(R+n)+1)*(N width)) (R+n) (reverse x)).mul
    (.refl _ polyOne)).trans (.of_coeff (RatPolyCoeffEqv.mul_one _))

private theorem right_source_separated {width R n : Nat}
    (y : IntrinsicExpression width) :
    PaddedPolynomialCoeffEqv ((2*(R+n)+1)*(N width))
      (sourcePolynomial
        (.mul (mirror (R+n) (chart (R+n) (unit width)))
          (chart (R+n) (advance n y))))
      (lowerSource R y) := by
  rw [chart_unit, chart_advance_add_center]
  change PaddedPolynomialCoeffEqv _ (polyMul polyOne (lowerSource R y)) _
  exact .of_coeff (RatPolyCoeffEqv.one_mul _)

/-- Finite connected covariance at one actual cutoff and boundary depth. -/
theorem originalWindowScalar_centered_abs_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (stage t n : Nat) (x y : IntrinsicExpression width) :
    let R := max x.radius y.radius
    Q'.abs
      (originalWindowScalar hw0 hw1 (2*(R+n))
          (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y))) stage t t +
        -(originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width))) stage t t *
          originalWindowScalar hw0 hw1 (2*(R+n))
            (.mul (mirror (R+n) (chart (R+n) (unit width)))
              (chart (R+n) (advance n y))) stage t t)) ≤
      separationCap x y * mixRate hw0 hw1 width ^ n := by
  let R := max x.radius y.radius
  have hx : x.radius ≤ R := Nat.le_max_left _ _
  have hy : y.radius ≤ R := Nat.le_max_right _ _
  let p := lowerSource R y
  let q := upperSource x
  have hp : SupportedQuaternionBlocks ((R+1)*(N width)) p :=
    source_supported R (chart R y) (chart_within R y hy)
  have hq : SupportedQuaternionBlocks ((R+n+1)*(N width)) q :=
    source_supported (R+n) (reverse x)
      (within_mono (Nat.le_add_right R n) _ (within_mono hx _ (reverse_within x)))
  have hpBig : SupportedQuaternionBlocks ((2*(R+n)+1)*(N width)) p :=
    support_mono hp (Nat.mul_le_mul_right (N width) (by omega))
  have hqLift : SupportedQuaternionBlocks ((2*(R+n)+1)*(N width))
      (liftBoundary ((R+n)*(N width)) q) := by
    have heq : (R+n+1)*(N width)+(R+n)*(N width) =
        (2*(R+n)+1)*(N width) := by
      rw [← Nat.add_mul]
      congr 1
      omega
    simpa only [heq] using lift_supported hq ((R+n)*(N width))
  have hb := polynomialWindow_covariance_bound hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) t R n (R+n) t p q hp hq
  have hlength : R+n+(R+n)=2*(R+n) := by omega
  rw [hlength] at hb
  have hj0 := originalWindowScalar_pin hw0 hw1 (2*(R+n))
    (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y)))
    ⟨mirror_within (R+n) (chart (R+n) x),
      within_mono (by omega : R+n ≤ 2*(R+n)) _
        (chart_within (R+n) (advance n y) (by change y.radius+n ≤ R+n; omega))⟩ stage t t
  have hl0 := originalWindowScalar_pin hw0 hw1 (2*(R+n))
    (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width)))
    ⟨mirror_within (R+n) (chart (R+n) x), True.intro⟩ stage t t
  have hr0 := originalWindowScalar_pin hw0 hw1 (2*(R+n))
    (.mul (mirror (R+n) (chart (R+n) (unit width)))
      (chart (R+n) (advance n y)))
    ⟨mirror_within (R+n) (chart (R+n) (unit width)),
      within_mono (by omega : R+n ≤ 2*(R+n)) _
        (chart_within (R+n) (advance n y) (by change y.radius+n ≤ R+n; omega))⟩ stage t t
  have hj1 := windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) t (2*(R+n)) t
    (source_supported _
      (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (advance n y)))
      ⟨mirror_within (R+n) (chart (R+n) x),
      within_mono (by omega : R+n ≤ 2*(R+n)) _
        (chart_within (R+n) (advance n y) (by change y.radius+n ≤ R+n; omega))⟩)
    (supported_polyMul hpBig hqLift)
    (mixed_source_separated x y hx)
  have hl1 := windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) t (2*(R+n)) t
    (source_supported _
      (.mul (mirror (R+n) (chart (R+n) x)) (chart (R+n) (unit width)))
      ⟨mirror_within (R+n) (chart (R+n) x), True.intro⟩)
    hqLift
    (left_source_separated x hx)
  have hr1 := windowRatio_padded_congr hw0 hw1 (headCutoff w+stage) width
    (Nat.le_add_right _ _) t (2*(R+n)) t
    (source_supported _
      (.mul (mirror (R+n) (chart (R+n) (unit width))) (chart (R+n) (advance n y)))
      ⟨mirror_within (R+n) (chart (R+n) (unit width)),
      within_mono (by omega : R+n ≤ 2*(R+n)) _
        (chart_within (R+n) (advance n y) (by change y.radius+n ≤ R+n; omega))⟩)
    hpBig
    (right_source_separated y)
  have hj := Q'.eqv_trans _ _ _ hj0 hj1
  have hl := Q'.eqv_trans _ _ _ hl0 hl1
  have hr := Q'.eqv_trans _ _ _ hr0 hr1
  have hleft := Q'.add_eqv_congr' hj (Q'.neg_eqv_congr _ _
    (Q'.eqv_trans _ _ _ (qmul hl hr) (Q'.mul_comm_eqv _ _)))
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.abs_eqv_congr hleft)) ?_
  exact Q'.le_trans' _ _ _ hb (Q'.le_of_eqv (by
    simp only [separationCap, upperSource, lowerSource]
    exact RingNormaliser.poly_identity_of_normal_eq
      (.mul (.add (.var 0) (.var 0)) (.mul (.var 2) (.add (.var 1) (.var 1))))
      (.mul (.mul (.add (.var 0) (.var 0)) (.add (.var 1) (.var 1))) (.var 2))
      (by decide) (fun
        | 0 => polynomialCap (upperSource x)
        | 1 => polynomialCap (lowerSource R y)
        | _ => mixRate hw0 hw1 width ^ n)))

/-- The literal-width all-nome centered pairing decays at the computed
finite-width transfer rate. -/
theorem intrinsic_centered_covariance_le {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (n : Nat) (x y : IntrinsicExpression width) :
    leEv
      (sub (intrinsicForm hw0 hw1 x (advance n y))
        (mul (intrinsicForm hw0 hw1 x (unit width))
          (intrinsicForm hw0 hw1 (unit width) y)))
      (ofQ' (separationCap x y * mixRate hw0 hw1 width ^ n)) := by
  let R := max x.radius y.radius
  let H := R+n
  let eXY := WindowExpression.mul (mirror H (chart H x)) (chart H (advance n y))
  let eXU := WindowExpression.mul (mirror H (chart H x)) (chart H (unit width))
  let eUY := WindowExpression.mul (mirror H (chart H (unit width))) (chart H (advance n y))
  have hXY := originalJoint_diagonal_converges hw0 hw1 (2*H) eXY
    ⟨mirror_within H (chart H x), within_mono (by omega : H ≤ 2*H) _
      (chart_within H (advance n y) (by change y.radius+n ≤ H; unfold H R; omega))⟩
  have hXU := originalJoint_diagonal_converges hw0 hw1 (2*H) eXU
    ⟨mirror_within H (chart H x), True.intro⟩
  have hUY := originalJoint_diagonal_converges hw0 hw1 (2*H) eUY
    ⟨mirror_within H (chart H (unit width)), within_mono (by omega : H ≤ 2*H) _
      (chart_within H (advance n y) (by change y.radius+n ≤ H; unfold H R; omega))⟩
  have hprod :=
    Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general hXU hUY
  have hconn := TrigAddCReal.convergesTo_add hXY (TrigAddCReal.convergesTo_neg hprod)
  have hbound := leEv_of_convergesTo_le hconn
    (convergesTo_const (ofQ' (separationCap x y * mixRate hw0 hw1 width ^ n)))
    (fun k => by
      have h := originalWindowScalar_centered_abs_le hw0 hw1 k k n x y
      apply leEv_le_ofQ'_of_approx_le
      intro j
      exact Q'.le_trans' _ _ _ (Q'.le_abs_self _) h)
  have hchartXY := intrinsicForm_chart hw0 hw1 x (advance n y) H
    (by unfold H R; omega) (by change y.radius+n ≤ H; unfold H R; omega)
  have hchartXU := intrinsicForm_chart hw0 hw1 x (unit width) H
    (by unfold H R; omega) (Nat.zero_le _)
  have hchartUY := intrinsicForm_chart hw0 hw1 (unit width) (advance n y) H
    (Nat.zero_le _) (by change y.radius+n ≤ H; unfold H R; omega)
  have hmarg := intrinsicForm_unit_invariant_right hw0 hw1 n y
  have hmul :=
    (CReal.mul_congr_left hchartXU).trans
      (TrigSignedAdd.mul_congr_right (hmarg.symm.trans hchartUY))
  exact leEv_trans (leEv_of_equiv
    (Equiv_add hchartXY (neg_congr hmul))) hbound

end YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance

#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.lowerSource
#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.upperSource
#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.separationCap
#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.separationCap_nonnegative
#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.originalWindowScalar_centered_abs_le
#print axioms YMGap.Continuum.BF4WilsonAllNomeSeparatedCovariance.intrinsic_centered_covariance_le
