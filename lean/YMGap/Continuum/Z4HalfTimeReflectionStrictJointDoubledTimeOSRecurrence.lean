/-
# Strict-cylinder doubled-time midpoint recurrence

The common-box source term in the derived doubled-time Young inequality is
identified with the original strict-cylinder quadratic by the explicit
base-transport limit.  Thus the reflection quadratic along literal Euclidean
time translations obeys the standard midpoint recurrence.  This is a
derived identity-and-positivity statement, not a covariance assumption.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSRecurrence

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSYoung
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The literal time-translate reflection quadratic satisfies the exact
doubled-time midpoint inequality in the eventual constructive-real order. -/
theorem timeTranslatedStrictJointReflectionQuadratic_midpointRecurrence
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv
      (CReal.mul (CReal.ofQ' 2)
        ((timeTranslateStrictJointCylinderVector shift vector).reflectionQuadratic
          hcoupling hle))
      (CReal.add
        (vector.reflectionQuadratic hcoupling hle)
        ((timeTranslateStrictJointCylinderVector (shift + shift) vector).reflectionQuadratic
          hcoupling hle)) := by
  have hsource : CReal.Equiv
      ((strictJointDoubledTimeMixedSource shift vector).reflectionQuadratic
        hcoupling hle)
      (vector.reflectionQuadratic hcoupling hle) :=
    boxTransportStrictJointCylinderVector_reflectionQuadratic_equiv
      hcoupling hle (shift + shift) vector
  have hright : CReal.Equiv
      (CReal.add
        ((strictJointDoubledTimeMixedSource shift vector).reflectionQuadratic
          hcoupling hle)
        ((strictJointDoubledTimeMixedTarget shift vector).reflectionQuadratic
          hcoupling hle))
      (CReal.add
        (vector.reflectionQuadratic hcoupling hle)
        ((timeTranslateStrictJointCylinderVector (shift + shift) vector).reflectionQuadratic
          hcoupling hle)) := by
    exact CReal.add_congr_left hsource
  exact
    (CReal.leEv_congr
      (CReal.Equiv.refl _)
      hright).mp
      (timeTranslatedStrictJointReflectionQuadratic_transportYoung
        hcoupling hle shift vector)

#print axioms timeTranslatedStrictJointReflectionQuadratic_midpointRecurrence

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSRecurrence
