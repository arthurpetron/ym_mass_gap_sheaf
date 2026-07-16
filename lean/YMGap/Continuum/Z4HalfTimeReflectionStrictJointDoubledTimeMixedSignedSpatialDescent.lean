/-
# Constructive-real descent for the signed spatial comparison

The finite-law and geometric comparison modulus for the strict doubled-time
pair now descends directly to equality of the corresponding constructive-real
presentation values.  No global translation-law hypothesis is used.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialComparison

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedRecoding
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialComparison
open YMGap.Continuum.Z4SignedCenteredRecedingPresentation
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4UniformShiftCenteredRecedingBridge

/-- The strict doubled-time translated diagonal and mixed signed
presentations define the same constructive-real value.  This is the direct
descent of the derived signed spatial comparison modulus. -/
theorem strictJointDoubledTime_signedSpatialValue_equiv
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling)
    {base shift stage : Nat} (hstage : shift + shift ≤ stage)
    {roots : List (List Nat)}
    (hroots : ∀ root, root ∈ roots →
      root ∈ canonicalSurfacePolymers base)
    (predicate : List Bool → Bool) :
    CReal.Equiv
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (timeTranslatedStrictJointSignedPresentation
          base shift stage roots predicate hroots))
      (couplingParametricSignedCenteredPresentationValueAtAnchor
        coupling hcoupling hle
        (strictJointDoubledTimeMixedSignedPresentation
          base shift stage roots predicate hstage hroots)) := by
  let target := timeTranslatedStrictJointSignedPresentation
    base shift stage roots predicate hroots
  let source := strictJointDoubledTimeMixedSignedPresentation
    base shift stage roots predicate hstage hroots
  change CReal.Equiv
    (couplingParametricSignedCenteredPresentationValueAtAnchor
      coupling hcoupling hle target)
    (couplingParametricSignedCenteredPresentationValueAtAnchor
      coupling hcoupling hle source)
  have htarget := signedCenteredPresentationVolumeModulus_of_anchor
    hcoupling hle target
  have hsource := signedCenteredPresentationVolumeModulus_of_anchor
    hcoupling hle source
  have hcomparison : SignedCenteredPresentationComparisonModulus
      coupling hcoupling target source := by
    exact strictJointDoubledTime_signedSpatialPresentationComparisonModulus
      hcoupling hle hstage hroots predicate
  exact couplingParametricSignedCenteredPresentationValue_equiv_of_comparison
    hcoupling hle htarget hsource hcomparison

#print axioms strictJointDoubledTime_signedSpatialValue_equiv

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedSignedSpatialDescent
