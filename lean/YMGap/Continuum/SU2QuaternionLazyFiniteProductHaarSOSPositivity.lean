/-
# Finite-product Haar positivity for lazy weighted polynomial SOS packets

A lazy rational-polynomial SOS packet stores each selected feature as a list
of raw polynomial factors.  The factor-product bridge turns that list into one
raw polynomial without expanding any concrete production packet.  This leaf
integrates the literal square of each such polynomial against the exact
finite product of quaternion-sphere moments, multiplies by the packet's
stored nonnegative weight, and sums over the packet's finite term carrier.

Uniform support in the first `4 * blockCount` scalar coordinates is exactly
the block-support premise of arbitrary finite-product Haar square positivity.
Consequently every summand is nonnegative, and a structural induction on
`finSum` proves nonnegativity of the complete weighted SOS moment.  No feature
term, packed index, face polynomial, or finite sum is evaluated or enumerated
in this argument.

The final theorem specializes the construction to the complete adjacent-even
fixed-face lazy density packet on its exact deduplicated active-link carrier.
It is a scalar fixed-plane density certificate for the rational product-sphere
functional.  It does not identify this scalar with the spin/fusion endpoint
kernel, prove a reflection-contraction identity, establish full reflection
positivity, take a continuum limit, or prove a Yang--Mills mass gap.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionLazyFactorProductBridge

namespace YMGap.Continuum.SU2QuaternionLazyFiniteProductHaarSOSPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier

/-! ## 1. Generic lazy-packet finite-product Haar value -/

/-- The exact finite-product quaternion-sphere value of a lazy finite
weighted polynomial SOS packet.  Each feature's factor list is first viewed
as one raw polynomial; only its literal raw square is passed to the moment
functional. -/
def lazyFiniteProductHaarSOSValue
    {Input : Type} {environment : Input → Nat → Q'}
    (blockCount : Nat)
    (packet : LazyRatPolySOSFeatures Input environment) : Q' :=
  finSum
    (fun term =>
      packet.data.weight term *
        finiteProductHaar blockCount
          (polyMul
            (lazyFeaturePolynomial packet term)
            (lazyFeaturePolynomial packet term)))
    packet.data.termCount

/-- A finite sum of pointwise nonnegative rational terms is nonnegative.
This local structural lemma avoids importing any unrelated summation layer. -/
private theorem finSum_nonnegative
    (summand : Nat → Q')
    (hsummand : ∀ term, (0 : Q') ≤ summand term) :
    ∀ termCount, (0 : Q') ≤ finSum summand termCount
  | 0 => Q'.le_refl' 0
  | termCount + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative summand hsummand termCount)
        (hsummand termCount)

/-- **Lazy finite-product Haar SOS positivity.**  If every factor in every
selected lazy feature is supported on the scalar coordinates of the stated
quaternion blocks, then the complete stored weighted sum of exact Haar
square moments is nonnegative. -/
theorem lazyFiniteProductHaarSOSValue_nonnegative
    {Input : Type} {environment : Input → Nat → Q'}
    (blockCount : Nat)
    (packet : LazyRatPolySOSFeatures Input environment)
    (hsupport : LazyPacketSupported (4 * blockCount) packet) :
    (0 : Q') ≤ lazyFiniteProductHaarSOSValue blockCount packet := by
  unfold lazyFiniteProductHaarSOSValue
  apply finSum_nonnegative
  intro term
  exact Q'.mul_nonneg _ _
    (packet.data.weight_nonnegative term)
    (finiteProductHaar_square_nonneg
      blockCount
      (lazyFeaturePolynomial packet term)
      ((supportedCoordinates_four_mul_iff
          blockCount (lazyFeaturePolynomial packet term)).mp
        (lazyFeaturePolynomial_supported hsupport term)))

/-! ## 2. Complete adjacent-even fixed-face density packet -/

/-- The full weighted lazy Haar SOS value of the adjacent-even fixed-face
density packet, on exactly one quaternion block per deduplicated active link. -/
def adjacentEvenFixedFaceLazyDensityHaarSOSValue
    (cutoff radius : Nat) : Q' :=
  lazyFiniteProductHaarSOSValue
    (adjacentEvenActiveLinks radius).length
    (adjacentEvenFixedFaceLazyDensityPacket cutoff radius)

/-- **Adjacent-even fixed-face lazy density certificate.**  The complete
weighted fixed-face lazy SOS has nonnegative exact active-link
product-sphere value.  The proof uses the production packet's exact support
certificate and never expands its mixed-radix term carrier. -/
theorem adjacentEvenFixedFaceLazyDensityHaarSOSValue_nonnegative
    (cutoff radius : Nat) :
    (0 : Q') ≤
      adjacentEvenFixedFaceLazyDensityHaarSOSValue cutoff radius := by
  unfold adjacentEvenFixedFaceLazyDensityHaarSOSValue
  apply lazyFiniteProductHaarSOSValue_nonnegative
  simpa [adjacentEvenActiveCoordinateCount] using
    (adjacentEvenFixedFaceLazyDensityPacket_supported cutoff radius)

#print axioms lazyFiniteProductHaarSOSValue_nonnegative
#print axioms adjacentEvenFixedFaceLazyDensityHaarSOSValue_nonnegative

end YMGap.Continuum.SU2QuaternionLazyFiniteProductHaarSOSPositivity
