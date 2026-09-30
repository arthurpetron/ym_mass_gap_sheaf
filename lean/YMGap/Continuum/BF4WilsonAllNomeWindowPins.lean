/- # Literal-width Wilson windows under the all-nome completed operations

Free source-polynomial identities descend through the original joint limit
at the same width.  The resulting embedded windows obey the actual all-nome
unit, linear, time, and time-zero multiplication laws.  No spatial-union
completion or small-nome form is used. -/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime
import YMGap.Continuum.BF4WilsonAllNomeLinearLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra

namespace YMGap.Continuum.BF4WilsonAllNomeWindowPins

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
  (shift shift_zero source_shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within chart_self unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (sum)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicAlgebra (smul)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowPaddedCongruence
  (windowRatio_padded_congr)
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison (headCutoff)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (commonForm intrinsicForm intrinsicForm_chart intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeSeminorm (seminorm)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (embed unitState)
open YMGap.Continuum.BF4WilsonAllNomeLinear
  (completedAdd completedSmul completedZero completedAdd_embed completedSmul_embed
    completedZero_embed completion_eq_of_pointwise)
open YMGap.Continuum.BF4WilsonAllNomeLinearLaws (completedSmul_zero)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedMultiply completedMultiply_embed)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_embed completedUnit_fixed)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier (multiply)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar (liftBoundary)
open YMGap.Continuum.SU2QuaternionAuxiliaryLiftAlgebra (lift_coeff)
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages

local notation:max "N" width:arg => List.length (baseLinks width)
local infix:50 " ≈ " => Q'.eqv

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat}

/-- Padded coefficient identity passes through the original *joint* limit.
The finite ratios retain their own full action and positive partition. -/
theorem originalJoint_padded_congr (L : Nat) (e f : WindowExpression width)
    (he : Within L e) (hf : Within L f)
    (h : PaddedPolynomialCoeffEqv ((L+1)*(N width))
      (sourcePolynomial e) (sourcePolynomial f)) :
    Equiv (originalJointLimit hw0 hw1 L e he)
      (originalJointLimit hw0 hw1 L f hf) :=
  Equiv_of_limit_of_equal
    (fun stage => SumOfSquares.Equiv_of_approx_eqv (fun _ =>
      Q'.eqv_trans _ _ _ (originalWindowScalar_pin hw0 hw1 L e he stage stage stage)
        (Q'.eqv_trans _ _ _
          (windowRatio_padded_congr hw0 hw1 _ width _ stage L stage
            (source_supported L e he) (source_supported L f hf) h)
          (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 L f hf stage stage stage)))))
    (originalJoint_diagonal_converges hw0 hw1 L e he)
    (originalJoint_diagonal_converges hw0 hw1 L f hf)

/-- An embedded finite window on the SAME literal-width all-nome carrier. -/
def embedWindow (H : Nat) (e : WindowExpression width) (he : Within H e) :
    BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width :=
  embed hw0 hw1 ⟨H,e,he⟩

private theorem intrinsicForm_source_right (H : Nat)
    (e f : WindowExpression width) (he : Within H e) (hf : Within H f)
    (hp : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial f))
    (z : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 z ⟨H,e,he⟩)
      (intrinsicForm hw0 hw1 z ⟨H,f,hf⟩) := by
  let x : IntrinsicExpression width := ⟨H,e,he⟩
  let y : IntrinsicExpression width := ⟨H,f,hf⟩
  let J := max z.radius H
  let blocks := (2*J+1)*(N width)
  have hz : z.radius ≤ J := Nat.le_max_left _ _
  have hx : x.radius ≤ J := Nat.le_max_right _ _
  have hy : y.radius ≤ J := Nat.le_max_right _ _
  have hxe : PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (chart J x))
      (liftBoundary ((J-H)*(N width)) (sourcePolynomial e)) := by
    simpa only [x, chart] using (source_shift blocks (J-H) e)
  have hyf : PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (chart J y))
      (liftBoundary ((J-H)*(N width)) (sourcePolynomial f)) := by
    simpa only [y, chart] using (source_shift blocks (J-H) f)
  have hxy : PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (chart J x)) (sourcePolynomial (chart J y)) :=
    hxe.trans ((PaddedPolynomialCoeffEqv.of_coeff
      (lift_coeff ((J-H)*(N width)) hp)).trans hyf.symm)
  have hsource : PaddedPolynomialCoeffEqv blocks
      (sourcePolynomial (.mul (mirror J (chart J z)) (chart J x)))
      (sourcePolynomial (.mul (mirror J (chart J z)) (chart J y))) :=
    (PaddedPolynomialCoeffEqv.refl blocks
      (sourcePolynomial (mirror J (chart J z)))).mul hxy
  have hlimit := originalJoint_padded_congr hw0 hw1 (2*J)
    (.mul (mirror J (chart J z)) (chart J x))
    (.mul (mirror J (chart J z)) (chart J y))
    ⟨mirror_within J (chart J z),
      within_mono (by omega : J ≤ 2*J) (chart J x) (chart_within J x hx)⟩
    ⟨mirror_within J (chart J z),
      within_mono (by omega : J ≤ 2*J) (chart J y) (chart_within J y hy)⟩
    (by simpa only [blocks] using hsource)
  have hl := intrinsicForm_chart hw0 hw1 z x J hz hx
  have hr := intrinsicForm_chart hw0 hw1 z y J hz hy
  have hm : Equiv
      (commonForm hw0 hw1 J (chart J z) (chart J x)
        (chart_within J z hz) (chart_within J x hx))
      (commonForm hw0 hw1 J (chart J z) (chart J y)
        (chart_within J z hz) (chart_within J y hy)) := by
    simpa only [commonForm] using hlimit
  exact hl.trans (hm.trans hr.symm)

/-- A free source-polynomial identity identifies windows in the actual
all-nome completion; it does not use the old spatial-union state. -/
theorem embedWindow_eq_of_source_identity (H : Nat)
    (e f : WindowExpression width) (he : Within H e) (hf : Within H f)
    (hp : RatPolyCoeffEqv (sourcePolynomial e) (sourcePolynomial f)) :
    embedWindow hw0 hw1 H e he = embedWindow hw0 hw1 H f hf := by
  unfold embedWindow
  apply completion_eq_of_pointwise hw0 hw1
  intro _ z
  exact (intrinsicForm_symm hw0 hw1 ⟨H,e,he⟩ z).trans
    ((intrinsicForm_source_right hw0 hw1 H e f he hf hp z).trans
      (intrinsicForm_symm hw0 hw1 ⟨H,f,hf⟩ z).symm)

/-- Every radius tag of the literal constant represents the same vacuum. -/
theorem embedWindow_one (H : Nat) :
    embedWindow hw0 hw1 H .one True.intro = unitState hw0 hw1 width := by
  have h := completedTime_embed hw0 hw1 H (unit width)
  change completedTime hw0 hw1 H (unitState hw0 hw1 width) =
    embed hw0 hw1 (advance H (unit width)) at h
  rw [completedUnit_fixed hw0 hw1 H] at h
  simpa only [embedWindow, BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit,
    advance, Nat.zero_add] using h.symm

theorem completedAdd_embedWindow (H : Nat) (e f : WindowExpression width)
    (he : Within H e) (hf : Within H f) :
    completedAdd hw0 hw1 (embedWindow hw0 hw1 H e he)
      (embedWindow hw0 hw1 H f hf) =
      embedWindow hw0 hw1 H (.add e f) ⟨he,hf⟩ := by
  unfold embedWindow
  rw [completedAdd_embed]
  simp only [sum, chart, Nat.max_self, Nat.sub_self, shift_zero]

theorem completedSmul_embedWindow (H : Nat) (c : Q')
    (e : WindowExpression width) (he : Within H e) :
    completedSmul hw0 hw1 c (embedWindow hw0 hw1 H e he) =
      embedWindow hw0 hw1 H (.smul c e) he := by
  unfold embedWindow
  rw [completedSmul_embed]
  rfl

theorem embedWindow_zero (H : Nat) :
    embedWindow hw0 hw1 H (.smul 0 .one) True.intro =
      completedZero hw0 hw1 width := by
  rw [← completedSmul_embedWindow hw0 hw1 H 0 .one True.intro,
    embedWindow_one, completedSmul_zero]

theorem completedMultiply_embedWindow (H : Nat) (L : SourceLoop width)
    (spin : Nat) (e : WindowExpression width) (he : Within H e) :
    completedMultiply hw0 hw1 L spin (embedWindow hw0 hw1 H e he) =
      embedWindow hw0 hw1 H (.mul (.loop H L spin) e)
        ⟨Nat.le_refl H, he⟩ := by
  unfold embedWindow
  rw [completedMultiply_embed]
  rfl

theorem completedTime_embedWindow (H n : Nat) (e : WindowExpression width)
    (he : Within H e) :
    completedTime hw0 hw1 n (embedWindow hw0 hw1 H e he) =
      embedWindow hw0 hw1 (H+n) e
        (within_mono (Nat.le_add_right _ _) e he) := by
  unfold embedWindow
  rw [completedTime_embed]
  rfl

#print axioms originalJoint_padded_congr
#print axioms embedWindow
#print axioms embedWindow_eq_of_source_identity
#print axioms embedWindow_one
#print axioms completedAdd_embedWindow
#print axioms completedSmul_embedWindow
#print axioms embedWindow_zero
#print axioms completedMultiply_embedWindow
#print axioms completedTime_embedWindow

end YMGap.Continuum.BF4WilsonAllNomeWindowPins
