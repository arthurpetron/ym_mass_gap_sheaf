/-
# Shift-one self-adjointness on the algebraic strict-cylinder direct limit

The adjacent-even argument proves one-step covariance for two vectors
presented in one source box.  This leaf co-presents arbitrary staged vectors
at their maximum base, uses the exact transport/time-translation commuting
square, and descends the result through both constructive-real and staged
quotients.  The outcome is self-adjointness of the shift-one action for the
existing `RC`-valued algebraic direct-limit reflection pairing.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCovariance
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepDirectLimitSelfAdjointness

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOneStepCovariance
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Staged common-box covariance -/

/-- Arbitrary staged vectors satisfy the one-step one-sided covariance law.
Both pairs are evaluated in `max left.base right.base + 1`; exact functoriality
of box transport and its exact commuting square with time translation identify
that common presentation with the finite-base covariance theorem. -/
theorem strictJointCylinderStage_oneSidedTimeCovariance_one_derived
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        left (right.timeTranslate 1))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        right (left.timeTranslate 1)) := by
  let outer := max left.base right.base
  have hleft : left.base ≤ outer := Nat.le_max_left _ _
  have hright : right.base ≤ outer := Nat.le_max_right _ _
  have houter : outer ≤ outer + 1 := Nat.le_add_right outer 1
  have hleftFinal : left.base ≤ outer + 1 := Nat.le_trans hleft houter
  have hrightFinal : right.base ≤ outer + 1 := Nat.le_trans hright houter
  have hleftShift : left.base + 1 ≤ outer + 1 :=
    Nat.add_le_add_right hleft 1
  have hrightShift : right.base + 1 ≤ outer + 1 :=
    Nat.add_le_add_right hright 1
  let leftCommon : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hleft left.vector
  let rightCommon : StrictJointCylinderVector outer :=
    boxTransportStrictJointCylinderVector hright right.vector
  have hforwardCommon : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector houter leftCommon)
        (timeTranslateStrictJointCylinderVector 1 rightCommon))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        left (right.timeTranslate 1)) := by
    rw [boxTransportStrictJointCylinderVector_trans hleft houter,
      timeTranslate_boxTransportStrictJointCylinderVector hright 1]
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left (right.timeTranslate 1)
        hleftFinal hrightShift
  have hreverseCommon : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector houter rightCommon)
        (timeTranslateStrictJointCylinderVector 1 leftCommon))
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        right (left.timeTranslate 1)) := by
    rw [boxTransportStrictJointCylinderVector_trans hright houter,
      timeTranslate_boxTransportStrictJointCylinderVector hleft 1]
    exact strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle right (left.timeTranslate 1)
        hrightFinal hleftShift
  have hcovariance : CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector houter leftCommon)
        (timeTranslateStrictJointCylinderVector 1 rightCommon))
      (strictJointCylinderReflectionBilinear hcoupling hle
        (boxTransportStrictJointCylinderVector houter rightCommon)
        (timeTranslateStrictJointCylinderVector 1 leftCommon)) := by
    exact strictJointOneSidedTimeCovariance_one_derived
      hcoupling hle leftCommon rightCommon
  exact CReal.Equiv.trans
    (CReal.Equiv.symm hforwardCommon)
    (CReal.Equiv.trans hcovariance hreverseCommon)

/-! ## 2. Symmetry of the staged and descended reflection pairing -/

/-- The staged maximum-common-box pairing is symmetric up to
constructive-real equivalence. -/
theorem strictJointCylinderStageReflectionBilinear_symm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle left right)
      (strictJointCylinderStageReflectionBilinear hcoupling hle right left) := by
  let outer := max left.base right.base
  have hleft : left.base ≤ outer := Nat.le_max_left _ _
  have hright : right.base ≤ outer := Nat.le_max_right _ _
  have hforward :=
    strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle left right hleft hright
  have hreverse :=
    strictJointCylinderStageReflectionBilinear_at_common
      hcoupling hle right left hright hleft
  have hsymmetry :=
    StrictJointCylinderVector.reflectionBilinear_symm
      hcoupling hle
      (boxTransportStrictJointCylinderVector hleft left.vector)
      (boxTransportStrictJointCylinderVector hright right.vector)
  exact CReal.Equiv.trans
    (CReal.Equiv.symm hforward)
    (CReal.Equiv.trans hsymmetry hreverse)

/-- The shift-one time action is already self-adjoint at the level of staged
representatives, up to constructive-real equivalence. -/
theorem strictJointCylinderStage_timeTranslate_one_selfAdjoint
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        (left.timeTranslate 1) right)
      (strictJointCylinderStageReflectionBilinear hcoupling hle
        left (right.timeTranslate 1)) :=
  CReal.Equiv.trans
    (strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle (left.timeTranslate 1) right)
    (CReal.Equiv.symm
      (strictJointCylinderStage_oneSidedTimeCovariance_one_derived
        hcoupling hle left right))

/-- Symmetry of the `RC`-valued reflection pairing on the algebraic direct
limit. -/
theorem StrictJointCylinderDirectLimit.reflectionBilinear_symm
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle left right =
      StrictJointCylinderDirectLimit.reflectionBilinear
        hcoupling hle right left := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftStage rightStage
  exact Quotient.sound
    (strictJointCylinderStageReflectionBilinear_symm
      hcoupling hle leftStage rightStage)

/-! ## 3. Direct-limit covariance and shift-one self-adjointness -/

/-- The finite-base covariance law descends to arbitrary algebraic
direct-limit vectors. -/
theorem StrictJointCylinderDirectLimit.oneSidedTimeCovariance_one_derived
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        left (StrictJointCylinderDirectLimit.timeTranslate 1 right) =
      StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        right (StrictJointCylinderDirectLimit.timeTranslate 1 left) := by
  refine Quotient.inductionOn₂ left right ?_
  intro leftStage rightStage
  exact Quotient.sound
    (strictJointCylinderStage_oneSidedTimeCovariance_one_derived
      hcoupling hle leftStage rightStage)

/-- The shift-one time action is self-adjoint for the algebraic direct-limit
reflection pairing. -/
theorem StrictJointCylinderDirectLimit.timeTranslate_one_selfAdjoint
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    (left right : StrictJointCylinderDirectLimit) :
    StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        (StrictJointCylinderDirectLimit.timeTranslate 1 left) right =
      StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        left (StrictJointCylinderDirectLimit.timeTranslate 1 right) := by
  calc
    StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        (StrictJointCylinderDirectLimit.timeTranslate 1 left) right =
      StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        right (StrictJointCylinderDirectLimit.timeTranslate 1 left) :=
      StrictJointCylinderDirectLimit.reflectionBilinear_symm
        hcoupling hle
        (StrictJointCylinderDirectLimit.timeTranslate 1 left) right
    _ = StrictJointCylinderDirectLimit.reflectionBilinear hcoupling hle
        left (StrictJointCylinderDirectLimit.timeTranslate 1 right) :=
      (StrictJointCylinderDirectLimit.oneSidedTimeCovariance_one_derived
        hcoupling hle left right).symm

#print axioms strictJointCylinderStage_oneSidedTimeCovariance_one_derived
#print axioms strictJointCylinderStageReflectionBilinear_symm
#print axioms strictJointCylinderStage_timeTranslate_one_selfAdjoint
#print axioms StrictJointCylinderDirectLimit.reflectionBilinear_symm
#print axioms StrictJointCylinderDirectLimit.oneSidedTimeCovariance_one_derived
#print axioms StrictJointCylinderDirectLimit.timeTranslate_one_selfAdjoint

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOneStepDirectLimitSelfAdjointness
