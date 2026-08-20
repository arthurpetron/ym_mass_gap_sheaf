/-
# Rational vector-space laws on the completed strict-cylinder OS carrier

The completed carrier already has addition, zero, negation, and a uniformly
continuous map for every rational scalar.  This file proves that the scalar
maps satisfy the actual module laws on the same quotient completion.  Each
law is first checked semantically on finite cylinder presentations, converted
to zero OS distance on staged vectors, and then descended pointwise through
arbitrary explicit-modulus Cauchy representatives.

No finite-state enumeration enters this layer.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalarLaws

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveLaws
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Semantic scalar laws on fixed-base presentations -/

theorem strictJointCylinderVector_smul_one_equivalent
    {base : Nat} (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent (vector.smul 1) vector := by
  intro radius support
  change
    (1 : Q') * vector.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base vector.roots support) ≈
      vector.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base vector.roots support)
  exact Q'.one_mul_eqv _

theorem strictJointCylinderVector_smul_zeroLike_equivalent
    {base : Nat} (vector zeroLike : StrictJointCylinderVector base)
    (hzero : ∀ bits, zeroLike.coefficient bits ≈ 0) :
    StrictJointCylinderVectorEquivalent (vector.smul 0) zeroLike := by
  intro radius support
  refine Q'.eqv_trans _ _ _ (QPoly.q_zero_mul _) ?_
  exact Q'.eqv_symm
    (hzero
      (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
        radius base zeroLike.roots support))

theorem strictJointCylinderVector_smul_mul_equivalent
    {base : Nat} (first second : Q')
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      ((vector.smul second).smul first) (vector.smul (first * second)) := by
  intro radius support
  change
    first *
        (second * vector.coefficient
          (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
            radius base vector.roots support)) ≈
      (first * second) *
        vector.coefficient
          (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
            radius base vector.roots support)
  exact Q'.eqv_symm (Q'.mul_assoc_eqv first second _)

theorem strictJointCylinderVector_add_scalar_smul_equivalent
    {base : Nat} (first second : Q')
    (vector : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (vector.smul (first + second))
      ((vector.smul first).add (vector.smul second)) := by
  intro radius support
  have htarget := StrictJointCylinderVector.add_coefficient_code
    (vector.smul first) (vector.smul second) radius support
  refine Q'.eqv_trans _ _ _ (QPoly.q_add_mul first second _) ?_
  exact Q'.eqv_symm htarget

theorem strictJointCylinderVector_smul_add_equivalent
    {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      ((left.add right).smul scalar)
      ((left.smul scalar).add (right.smul scalar)) := by
  intro radius support
  have hsource := StrictJointCylinderVector.add_coefficient_code
    left right radius support
  have htarget := StrictJointCylinderVector.add_coefficient_code
    (left.smul scalar) (right.smul scalar) radius support
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left scalar _ _ hsource) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_add_eqv scalar _ _) ?_
  exact Q'.eqv_symm htarget

/-! ## 2. Null scalar laws on staged vectors -/

private theorem boxTransportStrictJointCylinderVector_smul_of_le
    {base outer : Nat} (hbase : base <= outer)
    (scalar : Q') (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (vector.smul scalar) =
      (boxTransportStrictJointCylinderVector hbase vector).smul scalar := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_smul padding scalar vector

theorem strictJointCylinderStage_smul_one_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul 1 stage) stage)
      CReal.czero := by
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    (left := strictJointCylinderStageSmul 1 stage) (right := stage)
    (outer := stage.base) hcoupling hle (Nat.le_refl _) (Nat.le_refl _)
  change StrictJointCylinderVectorEquivalent
    (boxTransportStrictJointCylinderVector (Nat.le_refl _)
      (stage.vector.smul 1))
    (boxTransportStrictJointCylinderVector (Nat.le_refl _) stage.vector)
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_refl]
  exact strictJointCylinderVector_smul_one_equivalent stage.vector

theorem strictJointCylinderStage_smul_zero_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul 0 stage) strictJointCylinderStageZero)
      CReal.czero := by
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    (left := strictJointCylinderStageSmul 0 stage)
    (right := strictJointCylinderStageZero) (outer := stage.base)
    hcoupling hle (Nat.le_refl _) (Nat.zero_le _)
  change StrictJointCylinderVectorEquivalent
    (boxTransportStrictJointCylinderVector (Nat.le_refl _)
      (stage.vector.smul 0))
    (boxTransportStrictJointCylinderVector (Nat.zero_le _)
      (strictJointCylinderVectorZero 0))
  rw [boxTransportStrictJointCylinderVector_refl]
  apply strictJointCylinderVector_smul_zeroLike_equivalent
  intro bits
  exact Q'.eqv_refl 0

theorem strictJointCylinderStage_smul_mul_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Q') (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul first
          (strictJointCylinderStageSmul second stage))
        (strictJointCylinderStageSmul (first * second) stage))
      CReal.czero := by
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    (left := strictJointCylinderStageSmul first
      (strictJointCylinderStageSmul second stage))
    (right := strictJointCylinderStageSmul (first * second) stage)
    (outer := stage.base) hcoupling hle (Nat.le_refl _) (Nat.le_refl _)
  change StrictJointCylinderVectorEquivalent
    (boxTransportStrictJointCylinderVector (Nat.le_refl _)
      ((stage.vector.smul second).smul first))
    (boxTransportStrictJointCylinderVector (Nat.le_refl _)
      (stage.vector.smul (first * second)))
  rw [boxTransportStrictJointCylinderVector_refl,
    boxTransportStrictJointCylinderVector_refl]
  exact strictJointCylinderVector_smul_mul_equivalent first second stage.vector

theorem strictJointCylinderStage_add_scalar_smul_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Q') (stage : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul (first + second) stage)
        (strictJointCylinderStageAdd
          (strictJointCylinderStageSmul first stage)
          (strictJointCylinderStageSmul second stage)))
      CReal.czero := by
  have hright :
      (strictJointCylinderStageAdd
        (strictJointCylinderStageSmul first stage)
        (strictJointCylinderStageSmul second stage)).base <= stage.base := by
    simp [strictJointCylinderStageAdd, strictJointCylinderStageSmul]
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    (left := strictJointCylinderStageSmul (first + second) stage)
    (right := strictJointCylinderStageAdd
      (strictJointCylinderStageSmul first stage)
      (strictJointCylinderStageSmul second stage))
    (outer := stage.base) hcoupling hle (Nat.le_refl _) hright
  have htransport :
      boxTransportStrictJointCylinderVector hright
          (strictJointCylinderStageAdd
            (strictJointCylinderStageSmul first stage)
            (strictJointCylinderStageSmul second stage)).vector =
        (stage.vector.smul first).add (stage.vector.smul second) := by
    simpa [strictJointCylinderStageSmul,
      boxTransportStrictJointCylinderVector_refl] using
      (strictJointCylinderStage_add_transport
        (strictJointCylinderStageSmul first stage)
        (strictJointCylinderStageSmul second stage)
        (Nat.le_refl _) (Nat.le_refl _))
  change StrictJointCylinderVectorEquivalent
    (boxTransportStrictJointCylinderVector (Nat.le_refl _)
      (stage.vector.smul (first + second)))
    (boxTransportStrictJointCylinderVector hright
      (strictJointCylinderStageAdd
        (strictJointCylinderStageSmul first stage)
        (strictJointCylinderStageSmul second stage)).vector)
  rw [boxTransportStrictJointCylinderVector_refl, htransport]
  exact strictJointCylinderVector_add_scalar_smul_equivalent
    first second stage.vector

theorem strictJointCylinderStage_smul_add_null
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q') (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul scalar
          (strictJointCylinderStageAdd left right))
        (strictJointCylinderStageAdd
          (strictJointCylinderStageSmul scalar left)
          (strictJointCylinderStageSmul scalar right)))
      CReal.czero := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hsum : (strictJointCylinderStageAdd left right).base <= outer :=
    Nat.le_refl _
  have hscaledSum :
      (strictJointCylinderStageSmul scalar
        (strictJointCylinderStageAdd left right)).base <= outer := hsum
  have hsumScaled :
      (strictJointCylinderStageAdd
        (strictJointCylinderStageSmul scalar left)
        (strictJointCylinderStageSmul scalar right)).base <= outer :=
    Nat.le_refl _
  apply strictJointCylinderStage_dist_zero_of_common_equivalent
    (left := strictJointCylinderStageSmul scalar
      (strictJointCylinderStageAdd left right))
    (right := strictJointCylinderStageAdd
      (strictJointCylinderStageSmul scalar left)
      (strictJointCylinderStageSmul scalar right))
    (outer := outer) hcoupling hle hscaledSum hsumScaled
  have hsource :
      boxTransportStrictJointCylinderVector hsum
          (strictJointCylinderStageAdd left right).vector =
        (boxTransportStrictJointCylinderVector hleft left.vector).add
          (boxTransportStrictJointCylinderVector hright right.vector) :=
    strictJointCylinderStage_add_transport left right hleft hright
  have htarget :
      boxTransportStrictJointCylinderVector hsumScaled
          (strictJointCylinderStageAdd
            (strictJointCylinderStageSmul scalar left)
            (strictJointCylinderStageSmul scalar right)).vector =
        (boxTransportStrictJointCylinderVector hleft
          (strictJointCylinderStageSmul scalar left).vector).add
          (boxTransportStrictJointCylinderVector hright
            (strictJointCylinderStageSmul scalar right).vector) :=
    strictJointCylinderStage_add_transport
      (strictJointCylinderStageSmul scalar left)
      (strictJointCylinderStageSmul scalar right) hleft hright
  have hscaledSource :
      boxTransportStrictJointCylinderVector hscaledSum
          (strictJointCylinderStageSmul scalar
            (strictJointCylinderStageAdd left right)).vector =
        (boxTransportStrictJointCylinderVector hsum
          (strictJointCylinderStageAdd left right).vector).smul scalar :=
    boxTransportStrictJointCylinderVector_smul_of_le hsum scalar
      (strictJointCylinderStageAdd left right).vector
  have htarget' :
      boxTransportStrictJointCylinderVector hsumScaled
          (strictJointCylinderStageAdd
            (strictJointCylinderStageSmul scalar left)
            (strictJointCylinderStageSmul scalar right)).vector =
        ((boxTransportStrictJointCylinderVector hleft left.vector).smul scalar).add
          ((boxTransportStrictJointCylinderVector hright right.vector).smul scalar) := by
    rw [htarget]
    change
      (boxTransportStrictJointCylinderVector hleft
          (left.vector.smul scalar)).add
        (boxTransportStrictJointCylinderVector hright
          (right.vector.smul scalar)) = _
    rw [boxTransportStrictJointCylinderVector_smul_of_le hleft,
      boxTransportStrictJointCylinderVector_smul_of_le hright]
  rw [hscaledSource, htarget', hsource]
  exact strictJointCylinderVector_smul_add_equivalent scalar _ _

/-! ## 3. Scalar laws on all completion points -/

theorem strictJointCylinderCompletedSmul_one
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedSmul hcoupling hle 1 vector = vector := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_smul_one_null
      hcoupling hle (X.seq n))⟩

theorem strictJointCylinderCompletedSmul_zero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedSmul hcoupling hle 0 vector =
      strictJointCylinderCompletedZero hcoupling hle := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_smul_zero_null
      hcoupling hle (X.seq n))⟩

theorem strictJointCylinderCompletedSmul_mul
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Q')
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedSmul hcoupling hle first
        (strictJointCylinderCompletedSmul hcoupling hle second vector) =
      strictJointCylinderCompletedSmul hcoupling hle (first * second) vector := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_smul_mul_null
      hcoupling hle first second (X.seq n))⟩

theorem strictJointCylinderCompleted_add_scalar_smul
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (first second : Q')
    (vector : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedSmul hcoupling hle (first + second) vector =
      strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedSmul hcoupling hle first vector)
        (strictJointCylinderCompletedSmul hcoupling hle second vector) := by
  refine Quotient.inductionOn vector (fun X => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_add_scalar_smul_null
      hcoupling hle first second (X.seq n))⟩

theorem strictJointCylinderCompletedSmul_add
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q')
    (left right : StrictJointCylinderOSCompletion hcoupling hle) :
    strictJointCylinderCompletedSmul hcoupling hle scalar
        (strictJointCylinderCompletedAdd hcoupling hle left right) =
      strictJointCylinderCompletedAdd hcoupling hle
        (strictJointCylinderCompletedSmul hcoupling hle scalar left)
        (strictJointCylinderCompletedSmul hcoupling hle scalar right) := by
  refine Quotient.inductionOn left (fun X => ?_)
  refine Quotient.inductionOn right (fun Y => ?_)
  apply Quotient.sound
  exact ⟨SquaredSeminorm.NonexpansiveSemigroup.closeOfPointwiseNull
    (fun n => strictJointCylinderStage_smul_add_null
      hcoupling hle scalar (X.seq n) (Y.seq n))⟩

#print axioms strictJointCylinderVector_smul_one_equivalent
#print axioms strictJointCylinderVector_smul_zeroLike_equivalent
#print axioms strictJointCylinderVector_smul_mul_equivalent
#print axioms strictJointCylinderVector_add_scalar_smul_equivalent
#print axioms strictJointCylinderVector_smul_add_equivalent
#print axioms strictJointCylinderStage_smul_one_null
#print axioms strictJointCylinderStage_smul_zero_null
#print axioms strictJointCylinderStage_smul_mul_null
#print axioms strictJointCylinderStage_add_scalar_smul_null
#print axioms strictJointCylinderStage_smul_add_null
#print axioms strictJointCylinderCompletedSmul_one
#print axioms strictJointCylinderCompletedSmul_zero
#print axioms strictJointCylinderCompletedSmul_mul
#print axioms strictJointCylinderCompleted_add_scalar_smul
#print axioms strictJointCylinderCompletedSmul_add

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalarLaws
