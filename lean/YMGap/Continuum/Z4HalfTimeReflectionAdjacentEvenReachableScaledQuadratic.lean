/-
# The exact active reachable quadratic

The physical anchor matrix is a diagonal congruence of the reachable endpoint
matrix.  At the level of the quadratic form, the two diagonal factors are
therefore absorbed into the coefficient vector.  This file records that
identity and proves that positivity of the physical matrix is *equivalent* to
positivity of the reachable kernel on those scaled coefficient vectors.

This avoids requiring a Gram witness on reachable coordinates annihilated by
the physical outer factor.  It is an exact reformulation of the physical PSD
target, not a weaker positivity statement and not an assertion that the
remaining scaled inequality has already been proved.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic diagonal-congruence quadratic identity -/

private theorem scaledQuadraticTerm_regroup
    (leftCoefficient rightCoefficient leftScale rightScale entry : Q') :
    (leftCoefficient * rightCoefficient) *
        ((leftScale * rightScale) * entry) ≈
      ((leftCoefficient * leftScale) *
        (rightCoefficient * rightScale)) * entry := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.mul_assoc_eqv
      (leftCoefficient * rightCoefficient)
      (leftScale * rightScale) entry)) ?_
  apply Q'.mul_eqv_congr_right
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (leftCoefficient * rightCoefficient)
      (leftScale * rightScale))
    (mul4_rearrange leftScale rightScale
      leftCoefficient rightCoefficient)

/-- A diagonal kernel congruence is exactly coefficient scaling at the
quadratic-form level.  No sign, support, or invertibility premise is needed. -/
theorem gramQuadForm_diagonalKernelScale_eqv
    (kernel : Nat → Nat → Q') (scale coefficient : Nat → Q')
    (count : Nat) :
    gramQuadForm (diagonalKernelScale kernel scale)
        coefficient count ≈
      gramQuadForm kernel
        (fun index => coefficient index * scale index) count := by
  unfold gramQuadForm diagonalKernelScale
  apply finSum_eqv_congr
  intro left
  apply finSum_eqv_congr
  intro right
  exact scaledQuadraticTerm_regroup
    (coefficient left) (coefficient right)
    (scale left) (scale right) (kernel left right)

/-! ## 2. The physically active reachable target -/

/-- The reachable endpoint quadratic after absorbing the exact exterior
lower-half factors into the physical test vector. -/
def adjacentEvenReachableScaledQuadratic
    (K radius : Nat) (coefficient : Nat → Q') : Q' :=
  gramQuadForm
    (adjacentEvenReachableFixedInterfaceMatrix K radius)
    (fun index => coefficient index *
      adjacentEvenPhysicalOuterScale K radius index)
    (adjacentEvenPhysicalHalfStateCount K radius)

/-- The logically minimal reachable positivity proposition consumed by the
physical matrix.  It asks only for the scaled vectors that actually arise
after the exterior half weights are attached. -/
def AdjacentEvenReachableScaledPSD (K radius : Nat) : Prop :=
  ∀ coefficient : Nat → Q',
    (0 : Q') ≤ adjacentEvenReachableScaledQuadratic
      K radius coefficient

/-- Exact equality, up to rational representation, between the literal
physical anchor quadratic and the active reachable quadratic. -/
theorem adjacentEvenPhysicalReflectionQuadratic_anchor_eqv_reachableScaled
    (K radius : Nat) (coefficient : Nat → Q') :
    adjacentEvenPhysicalReflectionQuadratic
        anchorCoupling K radius coefficient ≈
      adjacentEvenReachableScaledQuadratic K radius coefficient := by
  unfold adjacentEvenPhysicalReflectionQuadratic
    adjacentEvenReachableScaledQuadratic
  refine Q'.eqv_trans _ _ _ ?_
    (gramQuadForm_diagonalKernelScale_eqv
      (adjacentEvenReachableFixedInterfaceMatrix K radius)
      (adjacentEvenPhysicalOuterScale K radius)
      coefficient
      (adjacentEvenPhysicalHalfStateCount K radius))
  unfold gramQuadForm
  apply finSum_eqv_congr
  intro left
  apply finSum_eqv_congr
  intro right
  exact Q'.mul_eqv_congr_left
    (coefficient left * coefficient right) _ _
    (adjacentEvenPhysicalReflectedMatrix_eqv_reachableDiagonal
      K radius left right)

/-- The active reachable statement is exactly equivalent to the full
physical anchor PSD proposition. -/
theorem adjacentEvenReachableScaledPSD_iff_physical
    (K radius : Nat) :
    AdjacentEvenReachableScaledPSD K radius ↔
      AdjacentEvenPhysicalAnchorPSD K radius := by
  constructor
  · intro hscaled coefficient
    exact Q'.le_trans' _ _ _
      (hscaled coefficient)
      (Q'.ge_of_eqv
        (adjacentEvenPhysicalReflectionQuadratic_anchor_eqv_reachableScaled
          K radius coefficient))
  · intro hphysical coefficient
    exact Q'.le_trans' _ _ _
      (hphysical coefficient)
      (Q'.le_of_eqv
        (adjacentEvenPhysicalReflectionQuadratic_anchor_eqv_reachableScaled
          K radius coefficient))

#print axioms gramQuadForm_diagonalKernelScale_eqv
#print axioms adjacentEvenPhysicalReflectionQuadratic_anchor_eqv_reachableScaled
#print axioms adjacentEvenReachableScaledPSD_iff_physical

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic
