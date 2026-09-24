/-
# All-nome centered variance of the literal dyadic Wilson square

The arbitrary selected-action word estimate is applied to the exact chain
action, ambient slab and time placement used by `originalWindowScalar`.
Passing its termwise lower bound to the existing original joint limit gives a
positive norm floor for the SAME centered vector in the literal all-nome
Wilson completion.

The floor is at fixed nome.  No comparison between widths, scaling survival,
or continuum statement is asserted.
-/

import YMGap.Continuum.BF4ExactSlabWilsonWordVariance
import YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry
import YMGap.Continuum.BF4WilsonAllNomeCenteredVector
import YMGap.Continuum.BF4WilsonAllNomeLoopTimePin

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabTemporalGaugeWilsonWord
open YMGap.Continuum.BF4ExactSlabFixedSpatialChainGeometry
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabLocalStarComparison (starRatio starRatio_positive)
open YMGap.Continuum.BF4ExactSlabWilsonWordVariance
open YMGap.Continuum.BF4DyadicWilsonSquare
open YMGap.Continuum.BF4DyadicWilsonSquarePlacedGeometry
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
open YMGap.Continuum.BF4WilsonAllNomeCenteredVector
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (equiv_sub joint_congr)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))

attribute [local irreducible] originalJointLimit originalWindowScalar intrinsicForm

/-- At every diagonal regulator stage, this is the variance of the exact
`chainIds` action and exact placed dyadic-square observable used by the
original window construction. -/
theorem originalWindowScalar_variance_floor
    (scale width stage : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let mean := originalWindowScalar hw0 hw1 0 (.loop 0 loop 1) stage stage stage
    starRatio w ≤
      originalWindowScalar hw0 hw1 0 (lagExpression loop 0) stage stage stage +
        -(mean*mean) := by
  let extent := width + (stage + (0 + stage))
  let ids := chainIds extent width 0 (stage + (0 + stage))
  have hambient : width ≤ extent := by omega
  have htime : stage ≤ extent := by omega
  have hfinite := finiteValue_variance_floor hw0 hw1 extent ids
    (fun _ hi => chainIds_physical hi) (chainIds_nodup extent width 0 (stage + (0 + stage)))
    (placedSelectedLink stage)
    (placedSelectedLink_physical scale width extent hwidth hambient stage htime)
    (placedDyadicTail scale stage)
    (placedDyadicTail_physical scale width extent hwidth hambient stage htime)
    (placedSelectedLink_not_mem_placedDyadicTail scale stage) stage
  simpa only [originalWindowScalar, lagExpression, placedPolynomial,
    Nat.zero_add, Nat.add_zero, paddedSquare_placed_edges_split,
    placedSelectedEdge, extent, ids] using hfinite

private theorem source_mean_coeff (scale width : Nat) (hwidth : side scale < width) :
    RatPolyCoeffEqv
      (sourcePolynomial (.mul
        (mirror 0 (.loop 0 (paddedSquare scale width hwidth) 1)) .one))
      (sourcePolynomial (.loop 0 (paddedSquare scale width hwidth) 1)) := by
  simp only [mirror, mapOffsets, sourcePolynomial]
  exact RatPolyCoeffEqv.mul_one _

private theorem ofQ_center (a b : Q') :
    Equiv (ofQ' (a + -(b*b)))
      (add (ofQ' a) (neg (mul (ofQ' b) (ofQ' b)))) := by
  apply SumOfSquares.Equiv_of_approx_eqv
  intro n
  exact RingNormaliser.poly_identity_of_normal_eq
    (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
    (.add (.var 0) (.neg (.mul (.var 1) (.var 1))))
    (by decide) (fun | 0 => a | _ => b)

/-- The literal dyadic Wilson mean is its original zero-window singleton
limit.  This is a chart identity inside the same all-nome form. -/
theorem literal_mean_pin (scale width : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let x := loopState loop
    Equiv (intrinsicForm hw0 hw1 x (unit width))
      (originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)) := by
  let loop := paddedSquare scale width hwidth
  let x := loopState loop
  have hchart := intrinsicForm_chart hw0 hw1 x (unit width) 0
    (Nat.le_refl 0) (Nat.le_refl 0)
  have hcongr := joint_congr hw0 hw1 0
    (.mul (mirror 0 (.loop 0 loop 1)) .one) (.loop 0 loop 1)
    ⟨Nat.le_refl 0, True.intro⟩ (Nat.le_refl 0)
    (source_mean_coeff scale width hwidth)
  exact hchart.trans (by
    simpa only [commonForm, loopState,
      BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit, chart,
      Nat.zero_sub,
      BF4ExactSlabFixedSpatialWilsonCenteredWindow.shift_zero] using hcongr)

/-- The termwise selected-action estimate survives in the exact original
joint limit. -/
theorem centered_scalar_floor
    (scale width : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let M := originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)
    leEv (ofQ' (starRatio w))
      (sub (lagMoment hw0 hw1 loop 0) (mul M M)) := by
  let loop := paddedSquare scale width hwidth
  let e : WindowExpression width := .loop 0 loop 1
  let M := originalJointLimit hw0 hw1 0 e (Nat.le_refl 0)
  have hdiag := originalJoint_diagonal_converges hw0 hw1 0
    (lagExpression loop 0) (lag_within loop 0)
  have hmean := originalJoint_diagonal_converges hw0 hw1 0 e (Nat.le_refl 0)
  have hcenter := TrigAddCReal.convergesTo_add hdiag
    (TrigAddCReal.convergesTo_neg
      (Z4HalfTimeReflectionStrictJointCRealCompletedCauchySchwarz.CReal.convergesTo_mul_general
        hmean hmean))
  exact leEv_of_convergesTo_le (convergesTo_const (ofQ' (starRatio w))) hcenter
    (fun stage => leEv_trans
      (leEv_of_le (ofQ'_le_ofQ'
        (originalWindowScalar_variance_floor hw0 hw1 scale width stage hwidth)))
      (leEv_of_equiv (ofQ_center
        (originalWindowScalar hw0 hw1 0 (lagExpression loop 0) stage stage stage)
        (originalWindowScalar hw0 hw1 0 e stage stage stage))))

/-- The exact scalar limit above is the centered moment of the literal
dyadic-square state. -/
theorem centered_norm_floor
    (scale width : Nat) (hwidth : side scale < width) :
    let loop := paddedSquare scale width hwidth
    let x := loopState loop
    leEv (ofQ' (starRatio w)) (centeredTimeMoment hw0 hw1 0 x x) := by
  let loop := paddedSquare scale width hwidth
  let x := loopState loop
  let M := originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)
  have hdiag := norm_pin hw0 hw1 loop
  have hm : Equiv (intrinsicForm hw0 hw1 x (unit width)) M :=
    literal_mean_pin hw0 hw1 scale width hwidth
  have hm' : Equiv (intrinsicForm hw0 hw1 (unit width) x) M :=
    (intrinsicForm_symm hw0 hw1 (unit width) x).trans hm
  have hcenter : Equiv (centeredTimeMoment hw0 hw1 0 x x)
      (sub (lagMoment hw0 hw1 loop 0) (mul M M)) := by
    unfold centeredTimeMoment
    rw [advance_zero]
    exact equiv_sub hdiag
      ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm'))
  exact leEv_trans (centered_scalar_floor hw0 hw1 scale width hwidth)
    (leEv_of_equiv hcenter.symm)

/-- Positive fixed-nome norm floor for the actual centered dyadic-square
vector in the existing all-nome Wilson completion. -/
theorem centeredVector_norm_floor
    (scale width : Nat) (hwidth : side scale < width) :
    let x := loopState (paddedSquare scale width hwidth)
    RCle (Quotient.mk crealSetoid (ofQ' (starRatio w)))
      (completedInner hw0 hw1 (centeredVector hw0 hw1 x)
        (centeredVector hw0 hw1 x)) := by
  dsimp only
  rw [centeredVector_diagonal]
  exact centered_norm_floor hw0 hw1 scale width hwidth

#print axioms originalWindowScalar_variance_floor
#print axioms literal_mean_pin
#print axioms centered_scalar_floor
#print axioms centered_norm_floor
#print axioms centeredVector_norm_floor

end YMGap.Continuum.BF4WilsonAllNomeDyadicVariance
