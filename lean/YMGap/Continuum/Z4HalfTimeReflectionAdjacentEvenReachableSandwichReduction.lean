/-
# Reachable sandwich reduction for the adjacent-even physical matrix

After deterministic endpoint collapse, the outer palindromic sandwich is
diagonal on the existing half-state index: the left and right coefficients
are the same canonical lower factor.  This leaf proves the generic
constructive diagonal Gram transport, identifies the complete zero-padded
physical matrix with that diagonal scaling of the reachable endpoint matrix,
and converts any reachable Gram witness into the exact physical PSD witness.

No reachable Gram witness is constructed here; that remains the common-middle
mathematical residual.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HeatKernelGramSOS
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic constructive diagonal Gram transport -/

def diagonalKernelScale
    (kernel : Nat → Nat → Q') (scale : Nat → Q')
    (left right : Nat) : Q' :=
  (scale left * scale right) * kernel left right

/-- A diagonal congruence of a constructive Gram is constructive Gram.  The
scale may have arbitrary rational signs; it is absorbed into the feature
vectors, so no square root or positivity assumption is needed. -/
def diagonalKernelScaleGramRep
    {kernel : Nat → Nat → Q'} (rep : GramRep kernel)
    (scale : Nat → Q') :
    GramRep (diagonalKernelScale kernel scale) where
  r := rep.r
  d := rep.d
  hd := rep.hd
  v := fun rank configuration =>
    scale configuration * rep.v rank configuration
  hM := by
    intro left right
    unfold diagonalKernelScale
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (scale left * scale right) _ _
        (rep.hM left right)) ?_
    refine Q'.eqv_trans _ _ _
      (const_mul_finSum
        (fun rank => rep.d rank *
          (rep.v rank left * rep.v rank right))
        (scale left * scale right) rep.r) ?_
    apply finSum_eqv_congr
    intro rank
    exact mul6_rearrange
      (scale left) (scale right) (rep.d rank)
      (rep.v rank left) (rep.v rank right)

/-! ## 2. Exact global physical-matrix identification -/

def adjacentEvenPhysicalOuterScale
    (K radius configuration : Nat) : Q' :=
  adjacentEvenLowerFactor anchorCoupling K radius
    (adjacentEvenPhysicalHalfStateAt K radius configuration)

theorem adjacentEvenPhysicalReflectedMatrix_eqv_reachableDiagonal
    (K radius left right : Nat) :
    adjacentEvenPhysicalReflectedMatrix
        anchorCoupling K radius left right ≈
      diagonalKernelScale
        (adjacentEvenReachableFixedInterfaceMatrix K radius)
        (adjacentEvenPhysicalOuterScale K radius)
        left right := by
  by_cases hleft : left < adjacentEvenPhysicalHalfStateCount K radius
  · by_cases hright : right < adjacentEvenPhysicalHalfStateCount K radius
    · rw [adjacentEvenPhysicalReflectedMatrix_eq_kernel
          anchorCoupling hleft hright]
      unfold diagonalKernelScale adjacentEvenPhysicalOuterScale
      rw [adjacentEvenReachableFixedInterfaceMatrix_eq_kernel
        hleft hright]
      refine Q'.eqv_trans _ _ _
        (adjacentEvenPhysicalReflectedKernel_anchor_eqv_reachableFactors
          (adjacentEvenPhysicalHalfStateAt_mem hleft)
          (adjacentEvenPhysicalHalfStateAt_mem hright)) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left
          (adjacentEvenLowerFactor anchorCoupling K radius
            (adjacentEvenPhysicalHalfStateAt K radius left)) _ _
          (Q'.mul_comm_eqv
            (adjacentEvenFixedInterfaceEndpointKernel K radius
              (adjacentEvenHalfStateEndpointAssignment radius
                (adjacentEvenPhysicalHalfStateAt K radius left))
              (adjacentEvenHalfStateEndpointAssignment radius
                (adjacentEvenPhysicalHalfStateAt K radius right)))
            (adjacentEvenLowerFactor anchorCoupling K radius
              (adjacentEvenPhysicalHalfStateAt K radius right)))) ?_
      exact Q'.eqv_symm
        (Q'.mul_assoc_eqv
          (adjacentEvenLowerFactor anchorCoupling K radius
            (adjacentEvenPhysicalHalfStateAt K radius left))
          (adjacentEvenLowerFactor anchorCoupling K radius
            (adjacentEvenPhysicalHalfStateAt K radius right))
          (adjacentEvenFixedInterfaceEndpointKernel K radius
            (adjacentEvenHalfStateEndpointAssignment radius
              (adjacentEvenPhysicalHalfStateAt K radius left))
            (adjacentEvenHalfStateEndpointAssignment radius
              (adjacentEvenPhysicalHalfStateAt K radius right))))
    · simpa [adjacentEvenPhysicalReflectedMatrix,
          adjacentEvenReachableFixedInterfaceMatrix,
          diagonalKernelScale, hleft, hright] using
        (Q'.eqv_symm (Q'.mul_zero_eqv
          (adjacentEvenPhysicalOuterScale K radius left *
            adjacentEvenPhysicalOuterScale K radius right)))
  · by_cases hright : right < adjacentEvenPhysicalHalfStateCount K radius
    · simpa [adjacentEvenPhysicalReflectedMatrix,
          adjacentEvenReachableFixedInterfaceMatrix,
          diagonalKernelScale, hleft, hright] using
        (Q'.eqv_symm (Q'.mul_zero_eqv
          (adjacentEvenPhysicalOuterScale K radius left *
            adjacentEvenPhysicalOuterScale K radius right)))
    · simpa [adjacentEvenPhysicalReflectedMatrix,
          adjacentEvenReachableFixedInterfaceMatrix,
          diagonalKernelScale, hleft, hright] using
        (Q'.eqv_symm (Q'.mul_zero_eqv
          (adjacentEvenPhysicalOuterScale K radius left *
            adjacentEvenPhysicalOuterScale K radius right)))

/-! ## 3. The exact conditional positivity bridge -/

/-- The sole remaining reachable Gram witness transports constructively to
the exact zero-padded physical anchor-coupling matrix. -/
def adjacentEvenPhysicalAnchorGramWitness_of_reachable
    (K radius : Nat)
    (rep : AdjacentEvenReachableFixedInterfaceGramWitness K radius) :
    AdjacentEvenPhysicalAnchorGramWitness K radius :=
  gramRep_of_eqv
    (diagonalKernelScaleGramRep rep
      (adjacentEvenPhysicalOuterScale K radius))
    (adjacentEvenPhysicalReflectedMatrix_eqv_reachableDiagonal
      K radius)

theorem adjacentEvenPhysicalAnchorPSD_of_reachable
    (K radius : Nat)
    (rep : AdjacentEvenReachableFixedInterfaceGramWitness K radius) :
    AdjacentEvenPhysicalAnchorPSD K radius :=
  adjacentEvenPhysicalAnchorPSD_of_gramRep
    K radius
    (adjacentEvenPhysicalAnchorGramWitness_of_reachable
      K radius rep)

#print axioms diagonalKernelScaleGramRep
#print axioms adjacentEvenPhysicalReflectedMatrix_eqv_reachableDiagonal
#print axioms adjacentEvenPhysicalAnchorGramWitness_of_reachable
#print axioms adjacentEvenPhysicalAnchorPSD_of_reachable

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction
