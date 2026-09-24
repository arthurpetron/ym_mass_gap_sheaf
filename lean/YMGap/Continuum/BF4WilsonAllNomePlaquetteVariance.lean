/-
# All-nome centered variance floor for the literal Wilson plaquette

The old face presentation and the literal Wilson plaquette have the same
original finite source for their mean.  Their diagonal moments are already
pinned to the same Wilson lag-zero moment.  Hence the existing local six-face
variance floor transfers as a scalar identity to the SAME literal-width
all-nome Wilson form.

This is a fixed-nome nontriviality witness for one actual plaquette.  It is
not an arbitrary-loop theorem, a nome-uniform scaling estimate, or a carrier
substitution.
-/

import YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
import YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
import YMGap.Continuum.BF4WilsonAllNomePlaquetteConnectedFloor

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq edgesOf)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter (faceSpan)
open YMGap.Continuum.BF4ExactSlabFixedSpatialSliceCarrier (baseLinks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialKineticMarginals (activeBlocks)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime
  (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
  (chartScalar chartScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointPairingLaws
  (jointPairing_symm)
open YMGap.Continuum.BF4ExactSlabFixedSpatialJointCenteredForm
  (jointCenteredMoment)
open YMGap.Continuum.BF4ExactSlabFixedSpatialLocalVariance
  (face_joint_variance_floor)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette
  (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonCenteredWindow
  (shift_zero)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm
  (chart chart_within)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws
  (windowRatio_congr)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (commonForm intrinsicForm intrinsicForm_chart intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin
  (loopState pairing_lag norm_pin)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity (lagMoment)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments
  (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonAllNomePlaquetteTimePin
  (jointPairing_lag)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws
  (equiv_sub joint_congr)
open YMGap.Continuum.BF4ExactSlabFixedSpatialPlaquetteUniformResponse
  (uniformFloor)
open YMGap.Continuum.BF4WilsonPlaquetteSourcePin
  (mixedProduct_mean)
open YMGap.Continuum.BF4ExactSlabLocalStarComparison
  (starRatio)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width)

local notation "p" => faceSpan width face hf
local notation "loop" => plaquetteLoop face hf
local notation "x" => loopState loop
local notation "u" => BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit width
local notation "J" => jointPairing hw0 hw1 width
local notation "F" => intrinsicForm hw0 hw1

attribute [local irreducible] chartScalar chartJointLimit jointPairing
  originalJointLimit originalWindowScalar intrinsicForm

private theorem source_mean_coeff :
    RatPolyCoeffEqv
      (sourcePolynomial (.mul (mirror 0 (.loop 0 loop 1)) .one))
      (sourcePolynomial (.loop 0 loop 1)) := by
  simp only [mirror, mapOffsets, sourcePolynomial]
  exact RatPolyCoeffEqv.mul_one _

/-- The literal Wilson mean is the original zero-window singleton mean.
No old completed carrier is used in this identification. -/
theorem literal_mean_pin :
    Equiv (F x u)
      (originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)) := by
  have hxu : (x).radius ≤ 0 := Nat.le_refl 0
  have huu : (u).radius ≤ 0 := Nat.le_refl 0
  have hchart := intrinsicForm_chart hw0 hw1 x u 0 hxu huu
  have hcongr := joint_congr hw0 hw1 0
    (.mul (mirror 0 (.loop 0 loop 1)) .one) (.loop 0 loop 1)
    ⟨Nat.le_refl 0, True.intro⟩ (Nat.le_refl 0)
    (source_mean_coeff (width := width) (face := face) (hf := hf))
  exact hchart.trans (by
    simpa only [commonForm, loopState,
      BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit, chart,
      Nat.zero_sub, shift_zero] using hcongr)

/-- The old face mean and literal Wilson mean use the same finite expectation
at every diagonal regulator index; only their convergence witnesses differ. -/
theorem mean_pin : Equiv (J p (unit width)) (F x u) := by
  have hp : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius (p).val ≤ 0 := by
    rw [BF4ExactSlabFixedSpatialFaceCharacter.faceSpan_radius]
    exact Nat.le_refl 0
  have hu : BF4ExactSlabFixedSpatialIntrinsicReflectedForm.radius (unit width).val ≤ 0 :=
    Nat.le_refl 0
  have hxu : (x).radius ≤ 0 := Nat.le_refl 0
  have huu : (u).radius ≤ 0 := Nat.le_refl 0
  have hold := jointPairing_chart hw0 hw1 width 0 p (unit width) hp hu
  have hnew := intrinsicForm_chart hw0 hw1 x u 0 hxu huu
  have hlimits : Equiv
      (chartJointLimit hw0 hw1 width 0 p (unit width) hp hu)
      (commonForm hw0 hw1 0 (chart 0 x) (chart 0 u)
        (chart_within 0 x hxu) (chart_within 0 u huu)) := by
    apply Equiv_of_limit_of_equal ?_
      (chartJoint_diagonal_converges hw0 hw1 width 0 p (unit width) hp hu)
      (by
        simpa only [commonForm, loopState,
          BF4ExactSlabFixedSpatialWilsonIntrinsicForm.unit, chart,
          Nat.zero_sub, shift_zero] using
          (originalJoint_diagonal_converges hw0 hw1 0
            (.mul (mirror 0 (.loop 0 loop 1)) .one)
            ⟨Nat.le_refl 0, True.intro⟩))
    intro stage
    apply SumOfSquares.Equiv_of_approx_eqv
    intro k
    exact Q'.eqv_trans _ _ _
      (chartScalar_pin hw0 hw1 width stage 0 p (unit width) hp hu stage)
      (Q'.eqv_trans _ _ _
        (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) stage 0 stage
          (mixedProduct_mean width face hf))
        (Q'.eqv_trans _ _ _
          (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _) stage 0 stage
            (source_mean_coeff (width := width) (face := face) (hf := hf)).symm)
          (Q'.eqv_symm (originalWindowScalar_pin hw0 hw1 0
            (.mul (mirror 0 (.loop 0 loop 1)) .one) ⟨Nat.le_refl 0, True.intro⟩
            stage stage stage))))
  exact hold.trans (hlimits.trans hnew.symm)

/-- Exact equality of the old local-star centered scalar and the centered
norm of the literal Wilson plaquette. -/
theorem centered_norm_pin :
    Equiv (jointCenteredMoment hw0 hw1 width 0 p p)
      (centeredTimeMoment hw0 hw1 0 x x) := by
  have hdiagOld := jointPairing_lag hw0 hw1 width face hf 0
  rw [BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime_zero] at hdiagOld
  have hdiagNew := norm_pin hw0 hw1 loop
  have hdiag : Equiv (J p p) (F x x) := hdiagOld.trans hdiagNew.symm
  have hm := mean_pin hw0 hw1 width face hf
  have hm' : Equiv (J (unit width) p) (F u x) :=
    (jointPairing_symm hw0 hw1 width (unit width) p).trans
      (hm.trans (intrinsicForm_symm hw0 hw1 x u))
  unfold jointCenteredMoment centeredTimeMoment
  rw [BF4ExactSlabFixedSpatialCompletedPhysicalTime.physicalTime_zero,
    BF4ExactSlabFixedSpatialWilsonPhysicalTime.advance_zero]
  exact Equiv_add hdiag (neg_congr
    ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm')))

/-- Width- and position-independent positive floor at every strict fixed nome. -/
theorem centered_norm_floor :
    leEv (ofQ' (starRatio w)) (centeredTimeMoment hw0 hw1 0 x x) :=
  leEv_trans (face_joint_variance_floor hw0 hw1 width face hf)
    (leEv_of_equiv (centered_norm_pin hw0 hw1 width face hf))

/-- The finite connected-response certificate is an actual lag-one response
of the SAME literal Wilson plaquette in the all-nome intrinsic form. -/
theorem centered_response_floor
    (hactive : ∀ l, l ∈ edgesOf face →
      (baseLinks width).idxOf l ∈ activeBlocks width) :
    leEv (ofQ' (uniformFloor hw0 width))
      (centeredTimeMoment hw0 hw1 1 x x) := by
  let M := originalJointLimit hw0 hw1 0 (.loop 0 loop 1) (Nat.le_refl 0)
  have hlag := pairing_lag hw0 hw1 loop 1
  have hm : Equiv (F x u) M := literal_mean_pin hw0 hw1 width face hf
  have hm' : Equiv (F u x) M :=
    (intrinsicForm_symm hw0 hw1 u x).trans hm
  have hcenter : Equiv (centeredTimeMoment hw0 hw1 1 x x)
      (sub (lagMoment hw0 hw1 loop 1) (mul M M)) := by
    unfold centeredTimeMoment
    exact equiv_sub hlag
      ((Pivot2.mul_congr_left hm).trans (Pivot2.mul_congr_right hm'))
  exact leEv_trans
    (BF4WilsonAllNomePlaquetteConnectedFloor.connected_response_floor
      hw0 hw1 width face hf hactive)
    (leEv_of_equiv hcenter.symm)

#print axioms literal_mean_pin
#print axioms mean_pin
#print axioms centered_norm_pin
#print axioms centered_norm_floor
#print axioms centered_response_floor

end YMGap.Continuum.BF4WilsonAllNomePlaquetteVariance
