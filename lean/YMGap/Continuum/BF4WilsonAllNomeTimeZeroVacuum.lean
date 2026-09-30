/-
# The completed all-nome time-zero Wilson character on the vacuum

The spin-index-one time-zero multiplier sends the existing unit state to the
literal fundamental Wilson-loop state in the SAME fixed-width all-nome
completion. Its completed-time autocorrelation is therefore the already
constructed original Wilson lag moment. This is a fixed-width, fixed-nome
consumer; it asserts no inter-width transport or continuum limit.
-/

import YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
import YMGap.Continuum.BF4WilsonAllNomeCompletedTime

namespace YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
  (shift)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (IntrinsicExpression chart chart_within chart_unit unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicSeminorm (difference)
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (commonForm intrinsicForm intrinsicForm_chart)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState)
open YMGap.Continuum.BF4WilsonAllNomeLinear (completion_eq_of_pointwise)
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner (embed unitState completedInner)
open YMGap.Continuum.BF4WilsonAllNomeTimeZeroOperator
  (completedMultiply completedMultiply_embed)
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
  (completedTime completedTime_loop_lag)
open YMGap.Continuum.BF4WilsonTimeZeroIntrinsicMultiplier
  (multiply multiply_radius chart_multiply)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  {width : Nat}

private theorem mirror_loop (loop : SourceLoop width) (H : Nat) :
    mirror H (.loop H loop 1) = .loop H loop 1 := by
  simp only [mirror, mapOffsets]
  congr 1
  exact (show 2*H-H=H by omega)

private theorem source_mul_unit_coeff (loop : SourceLoop width) (H : Nat)
    (z : IntrinsicExpression width) :
    RatPolyCoeffEqv
      (sourcePolynomial
        (.mul (mirror H (.mul (.loop H loop 1) .one)) (chart H z)))
      (sourcePolynomial (.mul (mirror H (.loop H loop 1)) (chart H z))) := by
  rw [show mirror H (.mul (.loop H loop 1) .one) =
      .mul (.loop H loop 1) .one by
        change WindowExpression.mul (mirror H (.loop H loop 1)) (mirror H .one) = _
        rw [mirror_loop]
        rfl]
  rw [show mirror H (.loop H loop 1) = .loop H loop 1 by
    exact mirror_loop loop H]
  simp only [sourcePolynomial]
  exact (RatPolyCoeffEqv.mul_one (sourcePolynomial (.loop H loop 1))).mul_right
    (sourcePolynomial (chart H z))

/-- Multiplying the constant state by the time-zero fundamental character is
the actual loop vector in the same literal-width reflected form. -/
private theorem multiply_unit_pairing (loop : SourceLoop width)
    (z : IntrinsicExpression width) :
    Equiv (intrinsicForm hw0 hw1 (multiply loop 1 (unit width)) z)
      (intrinsicForm hw0 hw1 (loopState loop) z) := by
  let H := z.radius
  have hunit : (unit width).radius ≤ H := by
    simp only [unit]
    exact Nat.zero_le _
  have hmul : (multiply loop 1 (unit width)).radius ≤ H := by
    simpa only [multiply_radius] using hunit
  have htest : z.radius ≤ H := Nat.le_refl _
  have hleft := intrinsicForm_chart hw0 hw1
    (multiply loop 1 (unit width)) z H hmul htest
  have hright := intrinsicForm_chart hw0 hw1 (loopState loop) z H
    (by simp only [loopState]; exact Nat.zero_le _)
    htest
  have hsource := joint_congr hw0 hw1 (2*H)
    (.mul (mirror H (.mul (.loop H loop 1) .one)) (chart H z))
    (.mul (mirror H (.loop H loop 1)) (chart H z))
    ⟨mirror_within H (.mul (.loop H loop 1) .one),
      within_mono (by omega) (chart H z) (chart_within H z htest)⟩
    ⟨mirror_within H (.loop H loop 1),
      within_mono (by omega) (chart H z) (chart_within H z htest)⟩
    (source_mul_unit_coeff loop H z)
  have hmiddle : Equiv
      (commonForm hw0 hw1 H (.mul (.loop H loop 1) .one) (chart H z)
        ⟨Nat.le_refl H, True.intro⟩ (chart_within H z htest))
      (commonForm hw0 hw1 H (.loop H loop 1) (chart H z)
        (Nat.le_refl H) (chart_within H z htest)) := by
    simpa only [commonForm] using hsource
  have hchartLoop : chart H (loopState loop) = .loop H loop 1 := by
    simp only [loopState, chart, shift, mapOffsets, Nat.zero_add, Nat.sub_zero]
  simp only [chart_multiply H loop 1 (unit width) hunit, chart_unit] at hleft
  simp only [hchartLoop] at hright
  exact hleft.trans (hmiddle.trans hright.symm)

/-- The all-nome completed time-zero multiplier sends the same unit state to
the literal fundamental Wilson-loop vector. -/
theorem completedMultiply_unitState (loop : SourceLoop width) :
    completedMultiply hw0 hw1 loop 1 (unitState hw0 hw1 width) =
      embed hw0 hw1 (loopState loop) := by
  rw [unitState, completedMultiply_embed]
  apply completion_eq_of_pointwise hw0 hw1
  intro _ z
  exact multiply_unit_pairing hw0 hw1 loop z

/-- Its same-carrier completed-time autocorrelation is exactly the original
all-nome lag moment. -/
theorem completedMultiply_unitState_lag (loop : SourceLoop width) (n : Nat) :
    completedInner hw0 hw1
        (completedMultiply hw0 hw1 loop 1 (unitState hw0 hw1 width))
        (completedTime hw0 hw1 n
          (completedMultiply hw0 hw1 loop 1 (unitState hw0 hw1 width))) =
      Quotient.mk crealSetoid (lagMoment hw0 hw1 loop n) := by
  rw [completedMultiply_unitState hw0 hw1 loop]
  exact completedTime_loop_lag hw0 hw1 loop n

#print axioms completedMultiply_unitState
#print axioms completedMultiply_unitState_lag
#print axioms multiply_unit_pairing

end YMGap.Continuum.BF4WilsonAllNomeTimeZeroVacuum
