/-
# Positivity of the even-time strict-cylinder transfer form

The derived doubled-time Osterwalder--Schrader identity says that the mixed
matrix coefficient between a cylinder and its translation by `2 * shift` is
the reflection quadratic of the intermediate translate.  Reflection
positivity therefore makes that mixed coefficient nonnegative.  Symmetry of
the reflection bilinear form gives the operator-oriented order
`<T^(2s)v,v> >= 0` after both vectors are put in the explicit common box.

This closes representative-level positivity for even time translations.  It
does not infer self-adjointness from positivity, and it does not construct the
fixed-carrier completion.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContractiveAction
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointEvenTimeOSPositive

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSIdentity
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-- The doubled-time mixed OS coefficient is nonnegative because it is
equivalent to the reflection quadratic of the intermediate translate. -/
theorem strictJointDoubledTimeMixedOSBilinear_leEv_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv CReal.czero
      (strictJointDoubledTimeMixedOSBilinear
        hcoupling hle shift vector) := by
  have hquadraticNonnegative :=
    StrictJointCylinderVector.reflectionQuadratic_geRat_zero
      hcoupling hle
      (timeTranslateStrictJointCylinderVector shift vector)
  have hquadratic : CReal.leEv CReal.czero
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector shift vector)) := by
    intro epsilon hepsilon
    obtain ⟨stage, hstage⟩ :=
      hquadraticNonnegative epsilon hepsilon
    exact ⟨stage, fun later hlater => hstage later hlater⟩
  have hidentity :=
    strictJointDoubledTimeMixedOSIdentity_derived
      hcoupling hle (Nat.le_refl (shift + shift)) vector
      (fixedStage := shift + shift)
  exact
    (CReal.leEv_congr (CReal.Equiv.refl _) hidentity).mp hquadratic

/-- Operator-oriented even-time positivity in the literal common box:
`<T^(2s)v,v> >= 0`.  The source presentation is zero-extended and the target
is the direct translation by `s+s`; no state-covariance premise is used. -/
theorem evenTimeStrictJointTransferForm_leEv_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (shift : Nat)
    (vector : StrictJointCylinderVector base) :
    CReal.leEv CReal.czero
      (strictJointCylinderReflectionBilinear hcoupling hle
        (timeTranslateStrictJointCylinderVector (shift + shift) vector)
        (boxTransportStrictJointCylinderVector
          (Nat.le_add_right base (shift + shift)) vector)) := by
  have hmixed :=
    strictJointDoubledTimeMixedOSBilinear_leEv_nonnegative
      hcoupling hle shift vector
  have hsymmetry :=
    StrictJointCylinderVector.reflectionBilinear_symm
      hcoupling hle
      (strictJointDoubledTimeMixedSource shift vector)
      (strictJointDoubledTimeMixedTarget shift vector)
  have hreversed : CReal.leEv CReal.czero
      (strictJointCylinderReflectionBilinear hcoupling hle
        (strictJointDoubledTimeMixedTarget shift vector)
        (strictJointDoubledTimeMixedSource shift vector)) :=
    (CReal.leEv_congr (CReal.Equiv.refl _) hsymmetry).mp hmixed
  exact hreversed

#print axioms strictJointDoubledTimeMixedOSBilinear_leEv_nonnegative
#print axioms evenTimeStrictJointTransferForm_leEv_nonnegative

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointEvenTimeOSPositive
