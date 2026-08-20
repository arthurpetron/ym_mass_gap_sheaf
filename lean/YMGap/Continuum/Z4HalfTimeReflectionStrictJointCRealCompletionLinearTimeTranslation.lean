/-
# Rational homogeneity of completed Euclidean-time translation

The completed strict-cylinder carrier has addition and rational scaling.  This
module proves that the actual completed time semigroup commutes with every
rational scalar.  Together with completed additivity, each time translate is
therefore a rational-linear map on the same OS carrier (stated through the two
literal laws rather than a bundled typeclass).
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionLinearTimeTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Staged time translation commutes with rational scaling already at the
algebraic direct-limit level. -/
theorem strictJointCylinderStage_timeTranslate_smul_equivalent
    (shift : Nat) (scalar : Q') (stage : StrictJointCylinderStage) :
    StrictJointCylinderStageEquivalent
      ((strictJointCylinderStageSmul scalar stage).timeTranslate shift)
      (strictJointCylinderStageSmul scalar (stage.timeTranslate shift)) := by
  refine ⟨stage.base + shift, Nat.le_refl _, Nat.le_refl _, ?_⟩
  change
    boxTransportStrictJointCylinderVector (Nat.le_refl _)
        (timeTranslateStrictJointCylinderVector shift
          (stage.vector.smul scalar)) =
      boxTransportStrictJointCylinderVector (Nat.le_refl _)
        ((timeTranslateStrictJointCylinderVector shift stage.vector).smul scalar)
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_refl]
  exact timeTranslateStrictJointCylinderVector_smul
    shift scalar stage.vector

theorem strictJointCylinderStage_timeTranslate_smul_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (scalar : Q') (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        ((strictJointCylinderStageSmul scalar stage).timeTranslate shift)
        (strictJointCylinderStageSmul scalar (stage.timeTranslate shift)))
      CReal.czero :=
  strictJointCylinderStageEquivalent_reflectionDistSq_zero hcoupling hle
    (strictJointCylinderStage_timeTranslate_smul_equivalent
      shift scalar stage)

/-- Every completed Euclidean-time translate is rational homogeneous. -/
theorem strictJointCylinderCompletedTimeTranslate_smul
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (scalar : Q')
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        (strictJointCylinderCompletedSmul hcoupling hle scalar vector) =
      strictJointCylinderCompletedSmul hcoupling hle scalar
        (strictJointCylinderCompletedTimeTranslate
          hcoupling hle shift vector) := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_timeTranslate_smul_null
      hcoupling hle shift scalar (X.seq n))⟩

#print axioms strictJointCylinderStage_timeTranslate_smul_equivalent
#print axioms strictJointCylinderStage_timeTranslate_smul_null
#print axioms strictJointCylinderCompletedTimeTranslate_smul

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionLinearTimeTranslation
