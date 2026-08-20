/-
# Additivity of completed strict-cylinder Euclidean-time translation

The base-independent strict OS completion now has a genuine additive carrier.
This module proves that the already constructed completed time semigroup acts
additively on that same carrier.  The representative identity is exact after
the harmless arithmetic reindexing

`max (leftBase + shift) (rightBase + shift) = max leftBase rightBase + shift`.

No spectral theorem or continuum Hamiltonian is asserted here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Maximum commutes with adding the same Euclidean-time shift. -/
private theorem max_add_shift
    (left right shift : Nat) :
    max (left + shift) (right + shift) = max left right + shift := by
  omega

private theorem boxTransportStrictJointCylinderVector_add_of_le
    {base outer : Nat} (hbase : base <= outer)
    (left right : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (left.add right) =
      (boxTransportStrictJointCylinderVector hbase left).add
        (boxTransportStrictJointCylinderVector hbase right) := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_add padding left right

/-- Time translation of a staged sum and the sum of the staged translates are
the same direct-limit presentation. -/
theorem strictJointCylinderStage_timeTranslate_add_equivalent
    (shift : Nat) (left right : StrictJointCylinderStage) :
    StrictJointCylinderStageEquivalent
      ((strictJointCylinderStageAdd left right).timeTranslate shift)
      (strictJointCylinderStageAdd
        (left.timeTranslate shift) (right.timeTranslate shift)) := by
  let outer := max left.base right.base + shift
  have hleftBase :
      ((strictJointCylinderStageAdd left right).timeTranslate shift).base <=
        outer := Nat.le_refl _
  have hrightBase :
      (strictJointCylinderStageAdd
        (left.timeTranslate shift) (right.timeTranslate shift)).base <=
        outer := by
    exact Nat.le_of_eq (max_add_shift left.base right.base shift)
  refine ⟨outer, hleftBase, hrightBase, ?_⟩
  unfold strictJointCylinderStageAdd StrictJointCylinderStage.timeTranslate
  rw [boxTransportStrictJointCylinderVector_refl]
  rw [timeTranslateStrictJointCylinderVector_add]
  rw [timeTranslate_boxTransportStrictJointCylinderVector,
    timeTranslate_boxTransportStrictJointCylinderVector]
  rw [boxTransportStrictJointCylinderVector_add_of_le]
  change
    (boxTransportStrictJointCylinderVector
        (Nat.add_le_add_right (Nat.le_max_left left.base right.base) shift)
        (timeTranslateStrictJointCylinderVector shift left.vector)).add
      (boxTransportStrictJointCylinderVector
        (Nat.add_le_add_right (Nat.le_max_right left.base right.base) shift)
        (timeTranslateStrictJointCylinderVector shift right.vector)) =
    (boxTransportStrictJointCylinderVector hrightBase
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_left (left.base + shift) (right.base + shift))
          (timeTranslateStrictJointCylinderVector shift left.vector))).add
      (boxTransportStrictJointCylinderVector hrightBase
        (boxTransportStrictJointCylinderVector
          (Nat.le_max_right (left.base + shift) (right.base + shift))
          (timeTranslateStrictJointCylinderVector shift right.vector)))
  congr 1
  · exact (boxTransportStrictJointCylinderVector_trans
      (Nat.le_max_left (left.base + shift) (right.base + shift))
      hrightBase (timeTranslateStrictJointCylinderVector shift left.vector)).symm
  · exact (boxTransportStrictJointCylinderVector_trans
      (Nat.le_max_right (left.base + shift) (right.base + shift))
      hrightBase (timeTranslateStrictJointCylinderVector shift right.vector)).symm

/-- The two staged presentations in the additive time-translation law have
zero OS distance. -/
theorem strictJointCylinderStage_timeTranslate_add_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat) (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        ((strictJointCylinderStageAdd left right).timeTranslate shift)
        (strictJointCylinderStageAdd
          (left.timeTranslate shift) (right.timeTranslate shift)))
      CReal.czero :=
  strictJointCylinderStageEquivalent_reflectionDistSq_zero hcoupling hle
    (strictJointCylinderStage_timeTranslate_add_equivalent shift left right)

/-- The actual completed Euclidean-time semigroup is additive on every point
of the same strict OS completion. -/
theorem strictJointCylinderCompletedTimeTranslate_additive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (shift : Nat)
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedTimeTranslate hcoupling hle shift
        (strictJointCylinderCompletedAdd hcoupling hle left right) =
      strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedTimeTranslate hcoupling hle shift left)
        (strictJointCylinderCompletedTimeTranslate hcoupling hle shift right) := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_timeTranslate_add_null
      hcoupling hle shift (X.seq n) (Y.seq n))⟩

#print axioms strictJointCylinderStage_timeTranslate_add_equivalent
#print axioms strictJointCylinderStage_timeTranslate_add_null
#print axioms strictJointCylinderCompletedTimeTranslate_additive

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation
