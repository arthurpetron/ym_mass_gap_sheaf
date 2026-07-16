/-
# Scheduled semantic descent for strict-cylinder time translation

The exact complete-lower-support query intertwiner is strong enough to
transport semantic coefficient equality on every radius used by the
reflection-form approximants.  This module records that cofinal/scheduled
descent and then descends the translated bilinear matrix coefficient and its
diagonal reflection seminorm.

It deliberately does not claim that the presentation translation preserves
`StrictJointCylinderVectorEquivalent` at every small radius, nor does it claim
translation invariance, contraction, or a semigroup law on a quotient.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4FiniteCylinderTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionLocalSupportPushforward
open YMGap.Continuum.Z4HalfTimeReflectionLowerSupportLocalQuery
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointMarkedCylinder
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationQueryTransport
open YMGap.Continuum.Z4HalfTimeReflectionStrictQueryGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftPhysicalTransport

local infix:50 " ≈ " => Q'.eqv

/-- Semantic equality is preserved at every radius enlarged together with
the time translation.  The reconstructed source support is independent of
the root family, so the same support can be passed to both presentations. -/
theorem timeTranslateStrictJointCylinderVector_coefficient_eqv_enlargedRadius
    {base : Nat}
    {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right)
    (shift radius : Nat) (hbase : strictQueryBase base ≤ radius)
    (targetSupport : List Nat) :
    (timeTranslateStrictJointCylinderVector shift left).coefficient
        (centralStrictLocalQueryCode (radius + shift) (base + shift)
          (timeTranslateStrictJointCylinderVector shift left).roots
          targetSupport) ≈
      (timeTranslateStrictJointCylinderVector shift right).coefficient
        (centralStrictLocalQueryCode (radius + shift) (base + shift)
          (timeTranslateStrictJointCylinderVector shift right).roots
          targetSupport) := by
  change left.coefficient
      (centralStrictLocalQueryCode (radius + shift) (base + shift)
        (left.roots.map (timeShiftCanonicalRoot shift base))
        targetSupport) ≈
    right.coefficient
      (centralStrictLocalQueryCode (radius + shift) (base + shift)
        (right.roots.map (timeShiftCanonicalRoot shift base))
        targetSupport)
  rw [centralStrictLocalQueryCode_timeShift_completeLowerSupport
    hbase left.rootsCanonical targetSupport]
  rw [centralStrictLocalQueryCode_timeShift_completeLowerSupport
    hbase right.rootsCanonical targetSupport]
  exact hequivalent radius
    (centralSpatialPullbackLowerSupport radius shift
      (centralLowerSupportAmbientFaces (radius + shift) targetSupport))

theorem strictQueryBase_add_shift
    (base shift : Nat) :
    strictQueryBase (base + shift) = strictQueryBase base + shift := by
  unfold strictQueryBase uniformPaddedBase
  omega

/-- Specialization to exactly the radius schedule used by every translated
reflection quadratic and bilinear approximant. -/
theorem timeTranslateStrictJointCylinderVector_coefficient_eqv_schedule
    {base : Nat}
    {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right)
    (shift stage : Nat) (targetSupport : List Nat) :
    (timeTranslateStrictJointCylinderVector shift left).coefficient
        (centralStrictLocalQueryCode
          (strictQueryBase (base + shift) + stage) (base + shift)
          (timeTranslateStrictJointCylinderVector shift left).roots
          targetSupport) ≈
      (timeTranslateStrictJointCylinderVector shift right).coefficient
        (centralStrictLocalQueryCode
          (strictQueryBase (base + shift) + stage) (base + shift)
          (timeTranslateStrictJointCylinderVector shift right).roots
          targetSupport) := by
  have hsource : strictQueryBase base ≤ strictQueryBase base + stage :=
    Nat.le_add_right _ _
  have htransport :=
    timeTranslateStrictJointCylinderVector_coefficient_eqv_enlargedRadius
      hequivalent shift (strictQueryBase base + stage) hsource targetSupport
  have hradius :
      (strictQueryBase base + stage) + shift =
        strictQueryBase (base + shift) + stage := by
    rw [strictQueryBase_add_shift]
    omega
  simpa only [hradius] using htransport

/-- Every rational approximant of the translated bilinear matrix coefficient
is independent of the chosen source presentations. -/
theorem reflectionBilinear_timeTranslate_approx_eqv_of_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right)).approx stage ≈
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left')
        (timeTranslateStrictJointCylinderVector shift right')).approx stage := by
  let radius := strictQueryBase (base + shift) + stage
  have hdirect :=
    centralNormalizedSupportReflectionBilinear_coefficient_eqv
      coupling hcoupling
      (centralStrictJointCenteredStageCutoff (base + shift) stage) radius
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius (base + shift)
          (timeTranslateStrictJointCylinderVector shift left).roots)
        (timeTranslateStrictJointCylinderVector shift left).coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius (base + shift)
          (timeTranslateStrictJointCylinderVector shift left').roots)
        (timeTranslateStrictJointCylinderVector shift left').coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius (base + shift)
          (timeTranslateStrictJointCylinderVector shift right).roots)
        (timeTranslateStrictJointCylinderVector shift right).coefficient)
      (centralLocalSupportCoefficient
        (centralStrictLocalQueryCode radius (base + shift)
          (timeTranslateStrictJointCylinderVector shift right').roots)
        (timeTranslateStrictJointCylinderVector shift right').coefficient)
      (fun support =>
        timeTranslateStrictJointCylinderVector_coefficient_eqv_schedule
          hleft shift stage support)
      (fun support =>
        timeTranslateStrictJointCylinderVector_coefficient_eqv_schedule
          hright shift stage support)
  exact Q'.eqv_trans _ _ _
    (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
      hcoupling hle
      (timeTranslateStrictJointCylinderVector shift left)
      (timeTranslateStrictJointCylinderVector shift right))
    (Q'.eqv_trans _ _ _ hdirect
      (Q'.eqv_symm
        (StrictJointCylinderVector.reflectionBilinear_approx_eqv_sequence
          hcoupling hle
          (timeTranslateStrictJointCylinderVector shift left')
          (timeTranslateStrictJointCylinderVector shift right'))))

/-- The translated bilinear matrix coefficient therefore descends through
source semantic equivalence in both arguments.  This is a well-definedness
result only; it asserts no translation invariance or norm bound. -/
theorem reflectionBilinear_timeTranslate_equiv_of_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift : Nat}
    {left left' right right' : StrictJointCylinderVector base}
    (hleft : StrictJointCylinderVectorEquivalent left left')
    (hright : StrictJointCylinderVectorEquivalent right right') :
    CReal.Equiv
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left)
        (timeTranslateStrictJointCylinderVector shift right))
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left')
        (timeTranslateStrictJointCylinderVector shift right')) := by
  intro epsilon hepsilon
  refine ⟨0, fun stage _ => ?_⟩
  have heqv :=
    reflectionBilinear_timeTranslate_approx_eqv_of_equivalent
      hcoupling hle (shift := shift) (stage := stage) hleft hright
  have hepsilonNonnegative : (0 : Q') ≤ epsilon := Q'.le_of_lt hepsilon
  exact ⟨
    Q'.le_trans' _ _ _ (Q'.le_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative),
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv heqv)
      (Q'.add_le_self_of_nonneg _ _ hepsilonNonnegative)⟩

/-- In particular, the translated reflection seminorm is independent of the
source presentation.  This uses the diagonal identity for the polarized form;
it still makes no assertion that translation preserves the seminorm. -/
theorem reflectionQuadratic_timeTranslate_equiv_of_equivalent
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift : Nat}
    {left right : StrictJointCylinderVector base}
    (hequivalent : StrictJointCylinderVectorEquivalent left right) :
    CReal.Equiv
      ((timeTranslateStrictJointCylinderVector shift left).reflectionQuadratic
        hcoupling hle)
      ((timeTranslateStrictJointCylinderVector shift right).reflectionQuadratic
        hcoupling hle) := by
  refine CReal.Equiv.trans
    (CReal.Equiv.symm
      (strictJointCylinderReflectionBilinear_self hcoupling hle
        (timeTranslateStrictJointCylinderVector shift left))) ?_
  refine CReal.Equiv.trans
    (reflectionBilinear_timeTranslate_equiv_of_equivalent
      hcoupling hle hequivalent hequivalent) ?_
  exact strictJointCylinderReflectionBilinear_self hcoupling hle
    (timeTranslateStrictJointCylinderVector shift right)

#print axioms timeTranslateStrictJointCylinderVector_coefficient_eqv_enlargedRadius
#print axioms strictQueryBase_add_shift
#print axioms timeTranslateStrictJointCylinderVector_coefficient_eqv_schedule
#print axioms reflectionBilinear_timeTranslate_approx_eqv_of_equivalent
#print axioms reflectionBilinear_timeTranslate_equiv_of_equivalent
#print axioms reflectionQuadratic_timeTranslate_equiv_of_equivalent

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointTimeTranslationSemanticDescent
