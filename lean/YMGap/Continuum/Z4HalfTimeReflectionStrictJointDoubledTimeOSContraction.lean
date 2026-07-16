/-
# Constructive contraction of translated strict reflection quadratics

The literal doubled-time midpoint recurrence and the derived coefficient cap
now meet the finite-orbit constructive-real Archimedean theorem.  Hence every
Euclidean time translate has reflection quadratic at most the untranslated
quadratic in the eventual order.
-/

import YMGap.Continuum.BoundedMidpointDoublingCReal
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSUniformCap

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BoundedMidpointDoublingCReal
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSRecurrence
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSUniformCap
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointGramLimitPositivity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- Reflection positivity, the doubled-time identity, and the derived finite
probability cap imply contraction for every literal time translate. -/
theorem timeTranslatedStrictJointReflectionQuadratic_leEv_source
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (shift : Nat) :
    CReal.leEv
      ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
        hcoupling hle)
      (vector.reflectionQuadratic hcoupling hle) := by
  let quadratic : Nat → CReal := fun displacement =>
    (timeTranslateStrictJointCylinderVector
      displacement vector).reflectionQuadratic hcoupling hle
  let bound := strictJointQuadraticUniformBound
    vector.roots.length vector.coefficient
  have hbound : ∀ displacement stage,
      (quadratic displacement).approx stage ≤ bound := by
    intro displacement stage
    exact timeTranslatedStrictJointReflectionQuadratic_approx_le_uniformBound
      hcoupling hle vector displacement stage
  have hanchor : ∀ stage, (0 : Q') ≤ (quadratic 0).approx stage := by
    intro stage
    dsimp only [quadratic]
    rw [timeTranslateStrictJointCylinderVector_zero]
    exact centralNormalizedStrictJointFixedQuadraticSequence_nonnegative
      coupling hcoupling base vector.roots vector.coefficient stage
  have hzeroQuadratic : CReal.Equiv
      (quadratic 0) (vector.reflectionQuadratic hcoupling hle) := by
    dsimp only [quadratic]
    rw [timeTranslateStrictJointCylinderVector_zero]
    exact CReal.Equiv.refl _
  have hmid : ∀ displacement,
      CReal.leEv
        (CReal.mul (CReal.ofQ' 2) (quadratic displacement))
        (CReal.add (quadratic 0) (quadratic (2 * displacement))) := by
    intro displacement
    have hdouble : displacement + displacement = 2 * displacement := by
      omega
    have htarget : CReal.Equiv
        ((timeTranslateStrictJointCylinderVector
          (displacement + displacement) vector).reflectionQuadratic
            hcoupling hle)
        ((timeTranslateStrictJointCylinderVector
          (2 * displacement) vector).reflectionQuadratic hcoupling hle) := by
      rw [hdouble]
      exact CReal.Equiv.refl _
    have hright : CReal.Equiv
        (CReal.add
          (vector.reflectionQuadratic hcoupling hle)
          ((timeTranslateStrictJointCylinderVector
            (displacement + displacement) vector).reflectionQuadratic
              hcoupling hle))
        (CReal.add (quadratic 0) (quadratic (2 * displacement))) := by
      exact
        (CReal.add_congr_left (CReal.Equiv.symm hzeroQuadratic)).trans
          (CReal.add_congr_right htarget)
    exact
      (CReal.leEv_congr (CReal.Equiv.refl _) hright).mp
        (timeTranslatedStrictJointReflectionQuadratic_midpointRecurrence
          hcoupling hle displacement vector)
  have hcontraction := bounded_midpointDoubling_leEv_anchor
    quadratic bound hbound hanchor hmid shift
  exact
    (CReal.leEv_congr (CReal.Equiv.refl _) hzeroQuadratic).mp
      hcontraction

#print axioms timeTranslatedStrictJointReflectionQuadratic_leEv_source

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction
