/-
# Generic original Wilson-window vacuum expectation at every strict nome

The completed all-nome vacuum pairing of an embedded finite signed Wilson
window is exactly its existing normalized original joint limit.  The extra
reflected chart is removed by the already proved source congruence and
time-padding theorem; no new functional, action, or quotient representative
is introduced.  This is fixed width and original lattice time.
-/

import YMGap.Continuum.BF4WilsonAllNomeWindowPins
import YMGap.Continuum.BF4WilsonJointFunctionalLaws
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity

namespace YMGap.Continuum.BF4WilsonAllNomeWindowExpectation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential (RatPolyCoeffEqv)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow (shift shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_unit chart_self unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonLimitStationarity (originalJoint_padding)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm (intrinsicForm commonForm intrinsicForm_chart)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
  (completedInner completedInner_embed unitState)
open YMGap.Continuum.BF4WilsonAllNomeWindowPins (embedWindow)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

attribute [local irreducible] intrinsicForm commonForm originalJointLimit

/-- The original normalized joint limit of EVERY bounded signed literal-width
Wilson window is its vacuum matrix element on the SAME all-nome completion. -/
theorem vacuum_embedWindow (H : Nat) (e : WindowExpression width) (he : Within H e) :
    completedInner hw0 hw1 (unitState hw0 hw1 width)
      (embedWindow hw0 hw1 H e he) =
      Quotient.mk crealSetoid (originalJointLimit hw0 hw1 H e he) := by
  let x : IntrinsicExpression width := ⟨H, e, he⟩
  have hchart : Equiv (intrinsicForm hw0 hw1 (unit width) x)
      (commonForm hw0 hw1 H .one e True.intro he) := by
    have h := intrinsicForm_chart hw0 hw1 (unit width) x H
      (by change 0 ≤ H; omega) (by change H ≤ H; omega)
    have hu : chart H (unit width) = (.one : WindowExpression width) := chart_unit width H
    have hx : chart H x = e := chart_self x
    simpa only [hu, hx] using h
  have hsource : RatPolyCoeffEqv
      (sourcePolynomial (.mul (mirror H (.one : WindowExpression width)) e))
      (sourcePolynomial e) := by
    change RatPolyCoeffEqv (polyMul polyOne (sourcePolynomial e)) (sourcePolynomial e)
    exact RatPolyCoeffEqv.one_mul _
  have hcongr : Equiv (commonForm hw0 hw1 H .one e True.intro he)
      (originalJointLimit hw0 hw1 (2*H) e
        (within_mono (by omega : H ≤ 2*H) e he)) := by
    unfold commonForm
    exact joint_congr hw0 hw1 (2*H) (.mul (mirror H .one) e) e
      ⟨mirror_within H .one, within_mono (by omega : H ≤ 2*H) e he⟩
      (within_mono (by omega : H ≤ 2*H) e he) hsource
  have hpad : Equiv
      (originalJointLimit hw0 hw1 (2*H) e
        (within_mono (by omega : H ≤ 2*H) e he))
      (originalJointLimit hw0 hw1 H e he) := by
    have h := originalJoint_padding hw0 hw1 H 0 H e he
    simpa only [show H+0+H=2*H by omega, shift_zero] using h
  change completedInner hw0 hw1 (unitState hw0 hw1 width)
    (BF4WilsonAllNomeCompletedInner.embed hw0 hw1 x) = _
  rw [BF4WilsonAllNomeCompletedInner.unitState, completedInner_embed]
  exact Quotient.sound (hchart.trans (hcongr.trans hpad))

#print axioms vacuum_embedWindow

end YMGap.Continuum.BF4WilsonAllNomeWindowExpectation
