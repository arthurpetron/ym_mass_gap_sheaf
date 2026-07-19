/-
# The direct adjacent-even boundary-character Haar quadratic

The fixed-face lazy density packet and the physical fixed-link endpoint
characters now live in one common active-link rational-polynomial carrier.
This leaf forms the direct Haar-side quadratic between them.

For arbitrary rational coefficients `coefficient`, first set

    C(U) = sum_s coefficient_s * outerScale_s * B_s(U),

where the sum runs over the production physical half-state carrier and
`B_s` is the factorized endpoint boundary character.  The implementation is
the requested `ratPolyFinSum`; it is kept opaque at concrete parameters.
Its evaluation, active-coordinate support, active-block support, and exact
finite-product Haar square positivity are proved constructively.

For every lazy density feature `p_t`, the dressed feature is the raw
polynomial `p_t * C`.  The production quadratic is

    sum_t weight_t * H((p_t * C)^2).

The proof of nonnegativity uses only the packet's stored weight certificate,
support closure, arbitrary supported-polynomial Haar square positivity, and
structural induction on the finite sum.  No packet term, endpoint state, raw
polynomial, or finite sum is enumerated or normalized.

This is the honest direct Haar-side quadratic.  No theorem in this file
identifies it with the reachable, fusion, trajectory, endpoint-kernel, or
physical reflection quadratic; that comparison remains a separate loopy
recoupling obligation.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
import YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction

namespace YMGap.Continuum.SU2QuaternionAdjacentEvenBoundaryCharacterHaarQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SU2ClassPolynomialAlgebra
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPoly
open YMGap.Continuum.SU2QuaternionGlobalFaceRatPolySupport
open YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
open YMGap.Continuum.SU2QuaternionLazyGlobalSOS
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceRatPolyRealization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointBoundaryCharacterRatPoly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction

local infix:50 " ≈ " => Q'.eqv

/-- Explicit local name for the physical rational SU(2) lattice field. -/
abbrev PhysicalGaugeField : Type :=
  YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAnchorFaceHolonomyPullback.RationalUnitQuaternionGaugeField

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. Constructive finite-sum support -/

/-- A finite raw-polynomial sum preserves any uniform coordinate support
bound on its summands. -/
theorem ratPolyFinSum_supportedCoordinates
    {coordinateCount : Nat} (polynomial : Nat → RatPoly)
    (hsupport : ∀ term,
      SupportedCoordinates coordinateCount (polynomial term)) :
    ∀ termCount,
      SupportedCoordinates coordinateCount
        (ratPolyFinSum polynomial termCount)
  | 0 => supportedCoordinates_polyZero coordinateCount
  | termCount + 1 => by
      change
        SupportedCoordinates coordinateCount
          (polyAdd (ratPolyFinSum polynomial termCount)
            (polynomial termCount))
      exact supportedCoordinates_polyAdd
        (ratPolyFinSum_supportedCoordinates
          polynomial hsupport termCount)
        (hsupport termCount)

/-- A finite sum of pointwise nonnegative rational values is nonnegative. -/
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

/-! ## 2. The coefficient-dependent physical boundary polynomial -/

/-- The requested coefficient-dependent physical endpoint polynomial

`C(U) = Σ_s (coefficient s * outerScale s) B_s(U)`.

This definition should remain opaque at concrete `K` and `radius`: the
symbolic finite sum is the intended carrier. -/
def adjacentEvenPhysicalBoundaryCoefficientPolynomial
    (K radius : Nat) (coefficient : Nat → Q') : RatPoly :=
  ratPolyFinSum
    (fun state =>
      polySmul
        (coefficient state *
          adjacentEvenPhysicalOuterScale K radius state)
        (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
          K radius state))
    (adjacentEvenPhysicalHalfStateCount K radius)

/-- Exact common-field evaluation of `C`: the polynomial finite sum is the
corresponding rational finite sum of scaled physical boundary characters. -/
theorem eval_adjacentEvenPhysicalBoundaryCoefficientPolynomial
    (K radius : Nat) (coefficient : Nat → Q')
    (field : PhysicalGaugeField) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenPhysicalBoundaryCoefficientPolynomial
          K radius coefficient) ≈
      finSum
        (fun state =>
          (coefficient state *
              adjacentEvenPhysicalOuterScale K radius state) *
            adjacentEvenPhysicalEndpointBoundaryCharacterValue
              K radius state field)
        (adjacentEvenPhysicalHalfStateCount K radius) := by
  unfold adjacentEvenPhysicalBoundaryCoefficientPolynomial
  refine Q'.eqv_trans _ _ _
    (eval_ratPolyFinSum
      (adjacentEvenActiveLinkEnvironment radius field)
      (fun state =>
        polySmul
          (coefficient state *
            adjacentEvenPhysicalOuterScale K radius state)
          (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
            K radius state))
      (adjacentEvenPhysicalHalfStateCount K radius)) ?_
  apply finSum_congr_eqv
  intro state
  refine Q'.eqv_trans _ _ _
    (evalRatPoly_smul
      (adjacentEvenActiveLinkEnvironment radius field)
      (coefficient state *
        adjacentEvenPhysicalOuterScale K radius state)
      (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
        K radius state)) ?_
  exact Q'.mul_eqv_congr_left
    (coefficient state *
      adjacentEvenPhysicalOuterScale K radius state) _ _
    (eval_adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial
      K radius state field)

/-- `C` stays inside the exact scalar-coordinate carrier of the production
active links. -/
theorem adjacentEvenPhysicalBoundaryCoefficientPolynomial_supported
    (K radius : Nat) (coefficient : Nat → Q') :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenPhysicalBoundaryCoefficientPolynomial
        K radius coefficient) := by
  unfold adjacentEvenPhysicalBoundaryCoefficientPolynomial
  apply ratPolyFinSum_supportedCoordinates
  intro state
  exact supportedCoordinates_polySmul _
    (adjacentEvenPhysicalEndpointBoundaryCharacterPolynomial_supported
      K radius state)

/-- Native finite-product-Haar block support of `C`. -/
theorem adjacentEvenPhysicalBoundaryCoefficientPolynomial_supportedBlocks
    (K radius : Nat) (coefficient : Nat → Q') :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
      (adjacentEvenPhysicalBoundaryCoefficientPolynomial
        K radius coefficient) := by
  rw [← supportedCoordinates_four_mul_iff]
  exact adjacentEvenPhysicalBoundaryCoefficientPolynomial_supported
    K radius coefficient

/-- The exact active-link finite-product Haar moment of `C^2`. -/
def adjacentEvenPhysicalBoundaryCoefficientHaarSquareMoment
    (K radius : Nat) (coefficient : Nat → Q') : Q' :=
  finiteProductHaar (adjacentEvenActiveLinks radius).length
    (polyMul
      (adjacentEvenPhysicalBoundaryCoefficientPolynomial
        K radius coefficient)
      (adjacentEvenPhysicalBoundaryCoefficientPolynomial
        K radius coefficient))

/-- Arbitrary rational boundary coefficients are allowed: positivity follows
because `C` is squared before applying the exact product-Haar functional. -/
theorem adjacentEvenPhysicalBoundaryCoefficientHaarSquareMoment_nonnegative
    (K radius : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤
      adjacentEvenPhysicalBoundaryCoefficientHaarSquareMoment
        K radius coefficient := by
  unfold adjacentEvenPhysicalBoundaryCoefficientHaarSquareMoment
  exact finiteProductHaar_square_nonneg
    (adjacentEvenActiveLinks radius).length
    (adjacentEvenPhysicalBoundaryCoefficientPolynomial
      K radius coefficient)
    (adjacentEvenPhysicalBoundaryCoefficientPolynomial_supportedBlocks
      K radius coefficient)

/-! ## 3. Dressing every lazy fixed-face feature -/

/-- The selected lazy fixed-face feature `p_t`, multiplied by the common
coefficient-dependent boundary polynomial `C`.  Keep this definition opaque
at concrete production parameters. -/
def adjacentEvenBoundaryDressedFeaturePolynomial
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) : RatPoly :=
  polyMul
    (lazyFeaturePolynomial
      (adjacentEvenFixedFaceLazyDensityPacket cutoff radius) term)
    (adjacentEvenPhysicalBoundaryCoefficientPolynomial
      K radius coefficient)

/-- Pointwise, the dressed polynomial is exactly the selected packet feature
times the physical boundary-character finite sum. -/
theorem eval_adjacentEvenBoundaryDressedFeaturePolynomial
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) (field : PhysicalGaugeField) :
    evalRatPoly (adjacentEvenActiveLinkEnvironment radius field)
        (adjacentEvenBoundaryDressedFeaturePolynomial
          cutoff K radius coefficient term) ≈
      (adjacentEvenFixedFaceLazyDensityPacket cutoff radius).data.feature
          term field *
        finSum
          (fun state =>
            (coefficient state *
                adjacentEvenPhysicalOuterScale K radius state) *
              adjacentEvenPhysicalEndpointBoundaryCharacterValue
                K radius state field)
          (adjacentEvenPhysicalHalfStateCount K radius) := by
  unfold adjacentEvenBoundaryDressedFeaturePolynomial
  refine Q'.eqv_trans _ _ _
    (evalRatPoly_mul
      (adjacentEvenActiveLinkEnvironment radius field)
      (lazyFeaturePolynomial
        (adjacentEvenFixedFaceLazyDensityPacket cutoff radius) term)
      (adjacentEvenPhysicalBoundaryCoefficientPolynomial
        K radius coefficient)) ?_
  exact q_mul_congr
    (eval_lazyFeaturePolynomial
      (adjacentEvenFixedFaceLazyDensityPacket cutoff radius)
      term field)
    (eval_adjacentEvenPhysicalBoundaryCoefficientPolynomial
      K radius coefficient field)

/-- Exact active-coordinate support of every dressed feature `p_t * C`. -/
theorem adjacentEvenBoundaryDressedFeaturePolynomial_supported
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) :
    SupportedCoordinates (adjacentEvenActiveCoordinateCount radius)
      (adjacentEvenBoundaryDressedFeaturePolynomial
        cutoff K radius coefficient term) := by
  unfold adjacentEvenBoundaryDressedFeaturePolynomial
  exact supportedCoordinates_polyMul
    (lazyFeaturePolynomial_supported
      (adjacentEvenFixedFaceLazyDensityPacket_supported cutoff radius)
      term)
    (adjacentEvenPhysicalBoundaryCoefficientPolynomial_supported
      K radius coefficient)

/-- Native active quaternion-block support of every dressed feature. -/
theorem adjacentEvenBoundaryDressedFeaturePolynomial_supportedBlocks
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) :
    SupportedQuaternionBlocks (adjacentEvenActiveLinks radius).length
      (adjacentEvenBoundaryDressedFeaturePolynomial
        cutoff K radius coefficient term) := by
  rw [← supportedCoordinates_four_mul_iff]
  exact adjacentEvenBoundaryDressedFeaturePolynomial_supported
    cutoff K radius coefficient term

/-- The exact product-Haar square moment of one dressed lazy feature. -/
def adjacentEvenBoundaryDressedFeatureHaarSquareMoment
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) : Q' :=
  finiteProductHaar (adjacentEvenActiveLinks radius).length
    (polyMul
      (adjacentEvenBoundaryDressedFeaturePolynomial
        cutoff K radius coefficient term)
      (adjacentEvenBoundaryDressedFeaturePolynomial
        cutoff K radius coefficient term))

/-- Each dressed feature contributes a nonnegative Haar square moment. -/
theorem adjacentEvenBoundaryDressedFeatureHaarSquareMoment_nonnegative
    (cutoff K radius : Nat) (coefficient : Nat → Q')
    (term : Nat) :
    (0 : Q') ≤
      adjacentEvenBoundaryDressedFeatureHaarSquareMoment
        cutoff K radius coefficient term := by
  unfold adjacentEvenBoundaryDressedFeatureHaarSquareMoment
  exact finiteProductHaar_square_nonneg
    (adjacentEvenActiveLinks radius).length
    (adjacentEvenBoundaryDressedFeaturePolynomial
      cutoff K radius coefficient term)
    (adjacentEvenBoundaryDressedFeaturePolynomial_supportedBlocks
      cutoff K radius coefficient term)

/-! ## 4. The production dressed weighted Haar quadratic -/

/-- The honest direct Haar-side quadratic

`sum_t weight_t * H((p_t * C)^2)`

for the complete adjacent-even fixed-face lazy density packet. -/
def adjacentEvenBoundaryCharacterDressedHaarQuadratic
    (cutoff K radius : Nat) (coefficient : Nat → Q') : Q' :=
  finSum
    (fun term =>
      (adjacentEvenFixedFaceLazyDensityPacket cutoff radius).data.weight term *
        adjacentEvenBoundaryDressedFeatureHaarSquareMoment
          cutoff K radius coefficient term)
    (adjacentEvenFixedFaceLazyDensityPacket cutoff radius).data.termCount

/-- **Direct Haar-side positivity.**  The complete weighted sum of dressed
active-link Haar squares is nonnegative for every rational coefficient
sequence.  This is structural square positivity only; it does not assert an
identification with any spin/fusion or reachable quadratic. -/
theorem adjacentEvenBoundaryCharacterDressedHaarQuadratic_nonnegative
    (cutoff K radius : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤
      adjacentEvenBoundaryCharacterDressedHaarQuadratic
        cutoff K radius coefficient := by
  unfold adjacentEvenBoundaryCharacterDressedHaarQuadratic
  apply finSum_nonnegative
  intro term
  exact Q'.mul_nonneg _ _
    ((adjacentEvenFixedFaceLazyDensityPacket
      cutoff radius).data.weight_nonnegative term)
    (adjacentEvenBoundaryDressedFeatureHaarSquareMoment_nonnegative
      cutoff K radius coefficient term)

#print axioms ratPolyFinSum_supportedCoordinates
#print axioms eval_adjacentEvenPhysicalBoundaryCoefficientPolynomial
#print axioms adjacentEvenPhysicalBoundaryCoefficientPolynomial_supportedBlocks
#print axioms adjacentEvenPhysicalBoundaryCoefficientHaarSquareMoment_nonnegative
#print axioms eval_adjacentEvenBoundaryDressedFeaturePolynomial
#print axioms adjacentEvenBoundaryDressedFeaturePolynomial_supportedBlocks
#print axioms adjacentEvenBoundaryDressedFeatureHaarSquareMoment_nonnegative
#print axioms adjacentEvenBoundaryCharacterDressedHaarQuadratic_nonnegative

end YMGap.Continuum.SU2QuaternionAdjacentEvenBoundaryCharacterHaarQuadratic
