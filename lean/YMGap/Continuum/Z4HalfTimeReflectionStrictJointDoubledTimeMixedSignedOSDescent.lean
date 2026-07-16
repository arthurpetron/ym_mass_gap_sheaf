/-
# Direct descent from the translated strict Gram limit to the mixed signed value

The cofinal OS recoding identifies the translated strict-joint centered limit
with the translated signed presentation.  Signed spatial descent identifies
that presentation with the doubled-time mixed signed presentation.  Their
composition removes every schedule and covariance interface before the final
mixed OS Gram-entry identification.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSDescent

set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCenteredLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSRecoding
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-- The actual translated strict Gram-entry limit is the doubled-time mixed
signed-presentation value.  No global covariance or comparison-modulus premise
appears in the statement. -/
theorem couplingParametricTranslatedStrictJointCenteredLimit_equiv_mixedSigned
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricStrictJointCenteredLimit
        coupling hcoupling hle predicate
        (timeShiftCanonicalRoots_canonical
          (base := base) (shift := shift) (roots := roots) hroots))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift stage roots predicate hstage hroots)) := by
  exact CReal.Equiv.trans
    (couplingParametricTranslatedStrictJointCenteredLimit_equiv_signedTarget
      hcoupling hle hroots predicate (fixedStage := stage))
    (strictJointDoubledTime_signedSpatialValue_equiv
      hcoupling hle hstage hroots predicate)

#print axioms couplingParametricTranslatedStrictJointCenteredLimit_equiv_mixedSigned

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedOSDescent
