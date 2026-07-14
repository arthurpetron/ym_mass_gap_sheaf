/-
# State-preserving period-two action for the canonical Wilson datum

The strict boundary exchange, exact Haar invariance, and literal invariance of
the retained Wilson kernel now combine into the selected Euclidean one-step
action on the constructed nonconstant reference weight.
-/

import YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity
import YMGap.Continuum.ReferenceWeightTimeGeometry

namespace YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ReferenceWeightTimeGeometry
open YMGap.Continuum.SU2QuaternionCanonicalEightCarrier
open YMGap.Continuum.SU2QuaternionCanonicalEightHaarSymmetry
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonWeight
open YMGap.Continuum.SU2QuaternionCanonicalEightWilsonPositivity

/-- Boundary exchange preserves every field of the constructed interacting
reference datum. -/
def canonicalRetainedBoundarySwapAction :
    ReferenceTranslationAction canonicalRetainedReferenceWeight where
  hom := canonicalBoundarySwapHom
  weight_fixed := retainedRelativeWeight8_swap_fixed
  reference_invariant := canonicalProductHaar_swap_invariant

theorem canonicalRetainedBoundarySwapAction_period_two (p : Poly8) :
    iterateTau canonicalRetainedBoundarySwapAction.hom.map 2 p = p := by
  exact swapPoly8_involutive p

theorem canonicalRetained_interacting_swap_invariant (p : Poly8) :
    (canonicalRetainedReferenceWeight.E_Λ
        (canonicalRetainedBoundarySwapAction.hom.map p)).eqv
      (canonicalRetainedReferenceWeight.E_Λ p) :=
  canonicalRetainedBoundarySwapAction.interacting_invariant p

end YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction

#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction.canonicalRetainedBoundarySwapAction
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction.canonicalRetainedBoundarySwapAction_period_two
#print axioms YMGap.Continuum.SU2QuaternionCanonicalEightTimeAction.canonicalRetained_interacting_swap_invariant
