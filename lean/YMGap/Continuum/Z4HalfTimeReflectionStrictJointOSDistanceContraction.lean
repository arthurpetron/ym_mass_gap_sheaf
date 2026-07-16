/-
# Squared-distance contraction for strict-cylinder time translation

The reflection quadratic of the presentation difference `left - right` is
the quotient-free squared distance associated with the strict OS seminorm.
Exact additivity and rational homogeneity of time translation identify the
translate of a difference with the difference of the translates.  The
one-vector OS contraction therefore yields a genuine pairwise distance
contraction, including its semigroup-step form.

This is the nonexpansiveness datum required to map Cauchy representatives and
descend through a metric quotient.  The remaining completion issue is the
construction of one fixed carrier from the base-indexed cylinder spaces.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContractiveAction

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContractiveAction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Presentation difference, using the already constructed append chart and
rational scaling. -/
def strictJointCylinderDifference
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVector base :=
  left.add (right.smul (-1))

/-- The strict OS squared distance between two presentations at one base. -/
def strictJointCylinderReflectionDistSq
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) : CReal :=
  (strictJointCylinderDifference left right).reflectionQuadratic
    hcoupling hle

/-- Translation commutes exactly with presentation difference. -/
theorem timeTranslateStrictJointCylinderVector_difference
    {base : Nat} (shift : Nat)
    (left right : StrictJointCylinderVector base) :
    timeTranslateStrictJointCylinderVector shift
        (strictJointCylinderDifference left right) =
      strictJointCylinderDifference
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right) := by
  unfold strictJointCylinderDifference
  rw [timeTranslateStrictJointCylinderVector_add]
  rw [timeTranslateStrictJointCylinderVector_smul]

/-- The squared distance is independent of semantically equivalent source
presentations in both arguments. -/
theorem strictJointCylinderReflectionDistSq_equiv_of_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq
        hcoupling hle left right)
      (strictJointCylinderReflectionDistSq
        hcoupling hle left' right') := by
  apply StrictJointCylinderVector.reflectionQuadratic_equiv
  exact strictJointCylinderVectorEquivalent_add hleft
    (strictJointCylinderVectorEquivalent_smul (-1) hright)

/-- Positive-time translation is nonexpansive for the strict OS squared
distance.  This is the representative-level Cauchy-map estimate. -/
theorem timeTranslatedStrictJointReflectionDistSq_leEv_source
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.leEv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (strictJointCylinderReflectionDistSq
        hcoupling hle left right) := by
  have hcontraction :=
    timeTranslatedStrictJointReflectionQuadratic_leEv_source
      hcoupling hle (strictJointCylinderDifference left right) shift
  rw [timeTranslateStrictJointCylinderVector_difference] at hcontraction
  exact hcontraction

/-- The distance contraction is compatible with the exact additive action:
an additional step contracts relative to the already translated pair. -/
theorem timeTranslatedStrictJointReflectionDistSq_leEv_previous
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base)
    (first second : Nat) :
    CReal.leEv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (timeTranslateStrictJointCylinderVector (first + second) left)
        (timeTranslateStrictJointCylinderVector (first + second) right))
      (strictJointCylinderReflectionDistSq hcoupling hle
        (timeTranslateStrictJointCylinderVector first left)
        (timeTranslateStrictJointCylinderVector first right)) := by
  have hcontraction :=
    timeTranslatedStrictJointReflectionQuadratic_leEv_previous
      hcoupling hle (strictJointCylinderDifference left right) first second
  rw [timeTranslateStrictJointCylinderVector_difference,
    timeTranslateStrictJointCylinderVector_difference] at hcontraction
  exact hcontraction

#print axioms timeTranslateStrictJointCylinderVector_difference
#print axioms strictJointCylinderReflectionDistSq_equiv_of_equivalent
#print axioms timeTranslatedStrictJointReflectionDistSq_leEv_source
#print axioms timeTranslatedStrictJointReflectionDistSq_leEv_previous

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
