/-
# The completed plaquette mean is the original Wilson singleton limit

The radius-zero common chart and the fixed Wilson singleton use the same
finite window ratio at every cutoff/depth diagonal.  Their existing
constructive limits therefore agree.  Nome and spatial width remain fixed;
this is not a spatial or spacing limit.
-/

import YMGap.Continuum.BF4WilsonPlaquetteSourcePin
import YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy

namespace YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.ClusterCount4DProgress (Z4Plaq)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFacePlacement (spatialFaces)
open YMGap.Continuum.BF4ExactSlabFixedSpatialFaceCharacter
  (faceSpan faceSpan_radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCompletedPhysicalTime (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialIntrinsicReflectedForm (radius)
open YMGap.Continuum.BF4ExactSlabFixedSpatialCommonChartCorrelator
  (chartScalar chartScalar_pin)
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialChartJointLimits
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPlaquette (plaquetteLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowTimeLimit
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4ExactSlabFixedSpatialWindowFunctionalLaws (windowRatio_congr)
open YMGap.Continuum.BF4WilsonPlaquetteSourcePin (mixedProduct_mean)

attribute [local irreducible]
  chartScalar chartJointLimit jointPairing originalJointLimit originalWindowScalar

/-- The completed fixed-width plaquette mean is the cutoff/time limit of the
literal original singleton Wilson insertion. -/
theorem jointPairing_mean {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (width : Nat) (face : Z4Plaq) (hf : face ∈ spatialFaces width) :
    Equiv
      (jointPairing hw0 hw1 width (faceSpan width face hf) (unit width))
      (originalJointLimit hw0 hw1 0 (.loop 0 (plaquetteLoop face hf) 1)
        (Nat.le_refl 0)) := by
  let x := faceSpan width face hf
  let e : WindowExpression width := .loop 0 (plaquetteLoop face hf) 1
  have hx : radius x.val ≤ 0 := by
    dsimp [x]
    rw [faceSpan_radius]
    exact Nat.le_refl 0
  have hu : radius (unit width).val ≤ 0 := Nat.le_refl 0
  have hlimits : Equiv
      (chartJointLimit hw0 hw1 width 0 x (unit width) hx hu)
      (originalJointLimit hw0 hw1 0 e (Nat.le_refl 0)) := by
    apply Equiv_of_limit_of_equal ?_
      (chartJoint_diagonal_converges hw0 hw1 width 0 x (unit width) hx hu)
      (originalJoint_diagonal_converges hw0 hw1 0 e (Nat.le_refl 0))
    intro stage
    apply SumOfSquares.Equiv_of_approx_eqv
    intro k
    exact Q'.eqv_trans _ _ _
      (chartScalar_pin hw0 hw1 width stage 0 x (unit width) hx hu stage)
      (Q'.eqv_trans _ _ _
        (windowRatio_congr hw0 hw1 _ width (Nat.le_add_right _ _)
          stage 0 stage (mixedProduct_mean width face hf))
        (Q'.eqv_symm
          (originalWindowScalar_pin hw0 hw1 0 e (Nat.le_refl 0)
            stage stage stage)))
  exact (jointPairing_chart hw0 hw1 width 0 x (unit width) hx hu).trans hlimits

end YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin

#print axioms YMGap.Continuum.BF4WilsonAllNomePlaquetteMeanPin.jointPairing_mean
