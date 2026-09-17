/-
# Original site reflection of signed scheduled Wilson-loop expressions

The existing mirror changes only time offsets. Every full ordered loop,
character spin, rational coefficient and sum/product operation is retained.
Structural recursion transports the literal source-loop reflection and
one-sidedness to the whole expression on the same original even slab.

The consumer is selected-action reflected positivity and the existing
explicit-modulus fixed-window time limit. No norm substitution, full spatial
union identification, spacing passage or continuum QFT is asserted.
-/

import YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
import YMGap.Continuum.BF4ExactSlabSpatialWilsonReflection

namespace YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection

set_option autoImplicit false

open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabSiteConditionalSquare
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry

/-- Exact original reflection, including arbitrary signed sums and products. -/
theorem placed_reflection {width radius A h : Nat}
    (hw : width ≤ adjacentEvenExtent radius) (hcenter : A+h=radius+1) :
    ∀ e : WindowExpression width, Within h e →
    ReflectionImage (adjacentEvenExtent radius)
      (placedPolynomial (adjacentEvenExtent radius) A e)
      (placedPolynomial (adjacentEvenExtent radius) A (mirror h e))
  | .one, _ => ReflectionImage.one _
  | .loop _offset value spin, he =>
      BF4ExactSlabSpatialWilsonReflection.placed_reflection hw hcenter he value spin
  | .add e f, he =>
      (placed_reflection hw hcenter e he.1).add (placed_reflection hw hcenter f he.2)
  | .mul e f, he =>
      (placed_reflection hw hcenter e he.1).mul (placed_reflection hw hcenter f he.2)
  | .smul c e, he => (placed_reflection hw hcenter e he).smul c

/-- Every original lower-window expression is one-sided, including its central slice. -/
theorem placed_oneSided {width radius A h : Nat}
    (hw : width ≤ adjacentEvenExtent radius) (hcenter : A+h=radius+1) :
    ∀ e : WindowExpression width, Within h e →
    OneSided radius (placedPolynomial (adjacentEvenExtent radius) A e)
  | .one, _ => BlockLocal.one _ _
  | .loop _offset value spin, he =>
      BF4ExactSlabSpatialWilsonReflection.placed_oneSided hw hcenter he value spin
  | .add e f, he =>
      BlockLocal.add (placed_oneSided hw hcenter e he.1) (placed_oneSided hw hcenter f he.2)
  | .mul e f, he =>
      BlockLocal.mul (placed_oneSided hw hcenter e he.1) (placed_oneSided hw hcenter f he.2)
  | .smul c e, he => BlockLocal.smul (placed_oneSided hw hcenter e he) c

#print axioms placed_reflection
#print axioms placed_oneSided

end YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowReflection
