/-
# The contractive indexed action of strict-cylinder time translation

The exact radius-indexed additive action and the constructive OS contraction
now meet.  Reindexing along arithmetic equality leaves the reflection
quadratic unchanged, so contraction from a translated source can be rewritten
as a genuine stepwise semigroup estimate.  Transitivity then gives an
iterated estimate back to the original vector.

This is the quotient-free, algebraic transfer action on strict-cylinder
presentations.  It does not yet construct the completed GNS operator or prove
its self-adjointness and positivity there.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContractiveAction

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContraction
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointRadiusIndexedTimeTranslationAction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The reflection form is insensitive to arithmetic reindexing -/

/-- Reindexing a presentation along an equality of base indices changes
neither its roots nor its coefficient table, hence not its reflection
quadratic. -/
theorem rebaseStrictJointCylinderVector_reflectionQuadratic_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {sourceBase targetBase : Nat} (hbase : sourceBase = targetBase)
    (vector : StrictJointCylinderVector sourceBase) :
    CReal.Equiv
      ((rebaseStrictJointCylinderVector hbase vector).reflectionQuadratic
        hcoupling hle)
      (vector.reflectionQuadratic hcoupling hle) := by
  cases hbase
  exact CReal.Equiv.refl _

/-! ## 2. Stepwise and iterated semigroup contraction -/

/-- Starting from an already translated vector, an additional time step is
contractive.  The left side is rewritten to the literal translation by the
sum using the exact indexed semigroup law. -/
theorem timeTranslatedStrictJointReflectionQuadratic_leEv_previous
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (first second : Nat) :
    CReal.leEv
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector (first + second) vector))
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector first vector)) := by
  have hsuccessive :=
    timeTranslatedStrictJointReflectionQuadratic_leEv_source
      hcoupling hle
      (timeTranslateStrictJointCylinderVector first vector) second
  have hrebase :=
    rebase_timeTranslateStrictJointCylinderVector_add first second vector
  have hrebaseForm :=
    rebaseStrictJointCylinderVector_reflectionQuadratic_equiv
      hcoupling hle (Nat.add_assoc base first second)
      (timeTranslateStrictJointCylinderVector second
        (timeTranslateStrictJointCylinderVector first vector))
  have hdirect : CReal.Equiv
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector (first + second) vector))
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector second
          (timeTranslateStrictJointCylinderVector first vector))) := by
    rw [← hrebase]
    exact hrebaseForm
  exact
    (CReal.leEv_congr hdirect (CReal.Equiv.refl _)).mpr hsuccessive

/-- Two successive time translations contract all the way back to the
untranslated source.  This is the first literal iterated-transfer estimate:
the semigroup step bound composes in the eventual constructive-real order. -/
theorem timeTranslatedStrictJointReflectionQuadratic_leEv_source_via_add
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base : Nat} (vector : StrictJointCylinderVector base)
    (first second : Nat) :
    CReal.leEv
      (StrictJointCylinderVector.reflectionQuadratic hcoupling hle
        (timeTranslateStrictJointCylinderVector (first + second) vector))
      (vector.reflectionQuadratic hcoupling hle) := by
  exact CReal.leEv_trans
    (timeTranslatedStrictJointReflectionQuadratic_leEv_previous
      hcoupling hle vector first second)
    (timeTranslatedStrictJointReflectionQuadratic_leEv_source
      hcoupling hle vector first)

#print axioms rebaseStrictJointCylinderVector_reflectionQuadratic_equiv
#print axioms timeTranslatedStrictJointReflectionQuadratic_leEv_previous
#print axioms timeTranslatedStrictJointReflectionQuadratic_leEv_source_via_add

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeOSContractiveAction
