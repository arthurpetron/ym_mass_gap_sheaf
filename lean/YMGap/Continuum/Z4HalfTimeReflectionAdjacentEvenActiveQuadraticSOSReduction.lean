/-
# Direct active-quadratic SOS reduction

The canonical compatibility contraction is exact, but a literal expansion
at each original fixed-face Gram rank is too restrictive: an individual rank
contribution need not even be symmetric.  The physically minimal target is
already the active reachable quadratic.  This leaf packages a direct finite
sum-of-squares certificate for that quadratic and transports it mechanically
to physical reflection positivity.

The certificate may mix all local face ranks and trajectory coordinates.
No inhabitant is asserted here; the intended construction is the explicit
Chebyshev/quaternion Haar SOS for the truncated anchor face weight.
-/

import YMGap.Constructive.SumOfSquares
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveQuadraticSOSReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A manifest finite weighted SOS -/

/-- One linear coordinate of the physical test vector. -/
def adjacentEvenActiveSOSLinear
    (amplitude : Nat → Nat → Q')
    (coefficient : Nat → Q')
    (stateCount term : Nat) : Q' :=
  finSum (fun state =>
    coefficient state * amplitude term state) stateCount

/-- A finite weighted sum of squares. -/
def adjacentEvenActiveSOS
    (weight : Nat → Q')
    (amplitude : Nat → Nat → Q')
    (coefficient : Nat → Q')
    (stateCount termCount : Nat) : Q' :=
  finSum (fun term =>
    weight term *
      (adjacentEvenActiveSOSLinear amplitude coefficient stateCount term *
        adjacentEvenActiveSOSLinear amplitude coefficient stateCount term))
    termCount

private theorem finSum_nonnegative_local
    (value : Nat → Q') (hvalue : ∀ index, (0 : Q') ≤ value index) :
    ∀ count, (0 : Q') ≤ finSum value count
  | 0 => Q'.le_refl' 0
  | count + 1 => by
      rw [finSum_succ]
      exact Q'.zero_le_add _ _
        (finSum_nonnegative_local value hvalue count)
        (hvalue count)

theorem adjacentEvenActiveSOS_nonnegative
    (weight : Nat → Q')
    (amplitude : Nat → Nat → Q')
    (coefficient : Nat → Q')
    (stateCount termCount : Nat)
    (hweight : ∀ term, (0 : Q') ≤ weight term) :
    (0 : Q') ≤ adjacentEvenActiveSOS
      weight amplitude coefficient stateCount termCount := by
  unfold adjacentEvenActiveSOS
  apply finSum_nonnegative_local
  intro term
  exact Q'.mul_nonneg _ _ (hweight term)
    (q_mul_self_nonneg
      (adjacentEvenActiveSOSLinear
        amplitude coefficient stateCount term))

/-! ## 2. Exact residual data and physical transport -/

/-- Sufficient direct SOS data for the physically active adjacent-even
quadratic.  Unlike the earlier rank-preserving adapter, `term` may encode a
fully mixed collection of face ranks, quaternion-polynomial square features,
Haar monomials, and trajectory decorations. -/
structure AdjacentEvenActiveQuadraticSOSData
    (K radius : Nat) : Type where
  termCount : Nat
  weight : Nat → Q'
  weight_nonnegative : ∀ term, (0 : Q') ≤ weight term
  amplitude : Nat → Nat → Q'
  factorization : ∀ coefficient : Nat → Q',
    adjacentEvenReachableScaledQuadratic K radius coefficient ≈
      adjacentEvenActiveSOS weight amplitude coefficient
        (adjacentEvenPhysicalHalfStateCount K radius) termCount

theorem AdjacentEvenActiveQuadraticSOSData.toReachableScaledPSD
    {K radius : Nat}
    (data : AdjacentEvenActiveQuadraticSOSData K radius) :
    AdjacentEvenReachableScaledPSD K radius := by
  intro coefficient
  exact Q'.le_trans' _ _ _
    (adjacentEvenActiveSOS_nonnegative
      data.weight data.amplitude coefficient
      (adjacentEvenPhysicalHalfStateCount K radius) data.termCount
      data.weight_nonnegative)
    (Q'.le_of_eqv (Q'.eqv_symm (data.factorization coefficient)))

theorem AdjacentEvenActiveQuadraticSOSData.toPhysicalPSD
    {K radius : Nat}
    (data : AdjacentEvenActiveQuadraticSOSData K radius) :
    AdjacentEvenPhysicalAnchorPSD K radius :=
  (adjacentEvenReachableScaledPSD_iff_physical K radius).mp
    data.toReachableScaledPSD

#print axioms adjacentEvenActiveSOS_nonnegative
#print axioms AdjacentEvenActiveQuadraticSOSData.toReachableScaledPSD
#print axioms AdjacentEvenActiveQuadraticSOSData.toPhysicalPSD

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveQuadraticSOSReduction
