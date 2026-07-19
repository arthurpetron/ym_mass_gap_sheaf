/-
# Finite-product Haar positivity for the adjacent-even lazy plane half

The selected adjacent-even reflection-plane feature is stored lazily as a
list of globally substituted face polynomials.  The factor-product bridge
packages that list as one raw polynomial supported on exactly the
deduplicated active-link quaternion blocks.  The arbitrary finite-product
polynomial theorem can therefore be applied directly to its literal raw
square.

This leaf records that application and its pointwise polynomial semantics.
It is only the plane-polynomial positivity input: it does not identify the
resulting finite-product sphere moment with the existing spin/fusion endpoint
kernel, prove the required reflection contraction identity, or establish the
full Wilson-density reflection-positivity theorem.

# Axiom gate

No `Classical`, choice, `sorry`/`admit`, `native_decide`, or custom axiom.
-/

import YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
import YMGap.Continuum.SU2QuaternionLazyFactorProductBridge

namespace YMGap.Continuum.SU2QuaternionAdjacentEvenLazyPlaneHaarPositivity

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarCarrier
open YMGap.Continuum.SU2QuaternionFiniteProductHaarFubini
open YMGap.Continuum.SU2QuaternionFiniteProductHaarPolynomialPositivity
open YMGap.Continuum.SU2QuaternionLazyFactorProductBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveLinkCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenLazyEndpointScaleAssembly

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-- The exact finite-product quaternion sphere moment of the literal raw
square of one selected adjacent-even lazy plane half. -/
def adjacentEvenLazyPlaneHaarSquareMoment
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) : Q' :=
  finiteProductHaar (adjacentEvenActiveLinks radius).length
    (polyMul
      (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
      (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm))

/-- The literal raw polynomial square evaluates pointwise to the rational
square of the established lazy plane-half value. -/
theorem eval_adjacentEvenLazyPlaneHalfPolynomial_square
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat)
    (rho : Nat → Q') :
    evalRatPoly rho
        (polyMul
          (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
          (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)) ≈
      adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho *
        adjacentEvenLazyPlaneHalfValue cutoff radius faceTerm rho := by
  refine Q'.eqv_trans _
    (evalRatPoly rho
        (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm) *
      evalRatPoly rho
        (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)) _
    (evalRatPoly_mul rho
      (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
      (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)) ?_
  exact q_mul_congr
    (eval_adjacentEvenLazyPlaneHalfPolynomial
      cutoff radius faceTerm rho)
    (eval_adjacentEvenLazyPlaneHalfPolynomial
      cutoff radius faceTerm rho)

/-- **Adjacent-even lazy plane polynomial positivity.**  The exact
active-link product-sphere moment of every selected plane-half square is
nonnegative. -/
theorem adjacentEvenLazyPlaneHaarSquareMoment_nonneg
    (cutoff radius : Nat) (faceTerm : PhysicalZ4Plaq → Nat) :
    (0 : Q') ≤
      adjacentEvenLazyPlaneHaarSquareMoment cutoff radius faceTerm := by
  unfold adjacentEvenLazyPlaneHaarSquareMoment
  exact finiteProductHaar_square_nonneg
    (adjacentEvenActiveLinks radius).length
    (adjacentEvenLazyPlaneHalfPolynomial cutoff radius faceTerm)
    (adjacentEvenLazyPlaneHalfPolynomial_supportedBlocks
      cutoff radius faceTerm)

#print axioms eval_adjacentEvenLazyPlaneHalfPolynomial_square
#print axioms adjacentEvenLazyPlaneHaarSquareMoment_nonneg

end YMGap.Continuum.SU2QuaternionAdjacentEvenLazyPlaneHaarPositivity
