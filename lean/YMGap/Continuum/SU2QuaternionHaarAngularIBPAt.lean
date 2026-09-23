/-
# Tangential integration by parts at an arbitrary quaternion block

Integrate the blocks preceding the selected block, commute its angular
derivative through that exact head-Haar prefix, and apply the existing head
integration-by-parts theorem.  All later blocks remain as polynomial-valued
spectators.  No support, positivity, or block-independence premise is used.
-/

import YMGap.Continuum.SU2QuaternionHaarTailDerivative

namespace YMGap.Continuum.SU2QuaternionHaarAngularIBPAt

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionFactorizedHaarContraction
open YMGap.Continuum.SU2QuaternionHaarAngularIBP
open YMGap.Continuum.SU2QuaternionHaarTailDerivative
open YMGap.Continuum.SU2QuaternionPartialSphereGaussian
open YMGap.Continuum.SU2QuaternionHaarHeadFubini
open YMGap.Continuum.SU2QuaternionHeadChainComposition
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumTransmittedMarginal
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private theorem partialHaarHeads_compose (first rest : Nat) (p : RatPoly) :
    partialHaarHeads (first + rest) p =
      partialHaarHeads rest (partialHaarHeads first p) := by
  induction first generalizing p with
  | zero => simp only [Nat.zero_add, partialHaarHeads]
  | succ first ih =>
      simpa only [Nat.succ_add, partialHaarHeads] using ih (partialHaarHead p)

/-- Integrating any prefix which contains the selected block annihilates its
tangential derivative coefficientwise.  This polynomial-valued form retains
all blocks after the prefix and is therefore stronger than scalar Haar
cancellation. -/
theorem partialHaarHeads_angularDerivative_at_zero
    {heads block i j : Nat} (hblock : block < heads)
    (hi : i < 4) (hj : j < 4) (polynomial : RatPoly) :
    RatPolyCoeffEqv
      (partialHaarHeads heads
        (angularDerivative (4 * block + i) (4 * block + j) polynomial))
      polyZero := by
  let rest := heads - (block + 1)
  have hn : block + 1 + rest = heads := by
    dsimp [rest]
    omega
  rw [← hn, partialHaarHeads_compose (block + 1) rest,
    partialHaarHeads_compose block 1]
  have hhead : RatPolyCoeffEqv
      (partialHaarHeads 1
        (partialHaarHeads block
          (angularDerivative (4 * block + i) (4 * block + j) polynomial)))
      polyZero := by
    simp only [partialHaarHeads]
    exact (partialHaarHead_congr
      (angularDerivative_partialHaarHeads block i j polynomial).symm).trans
        (partialHaarHead_angularDerivative_zero hi hj
          (partialHaarHeads block polynomial))
  exact (partialHaarHeads_congr rest hhead).trans (by
    induction rest with
    | zero => exact RatPolyCoeffEqv.refl _
    | succ rest ih =>
        simpa only [partialHaarHeads] using ih)

/-- The tangential vector field in any in-range quaternion block has zero
integral under the original finite product Haar functional. -/
theorem quaternionHaar_angularDerivative_at
    {n block i j : Nat} (hblock : block < n) (hi : i < 4) (hj : j < 4)
    (polynomial : RatPoly) :
    quaternionHaar n
      (angularDerivative (4 * block + i) (4 * block + j) polynomial) ≈ 0 := by
  let tail := n - (block + 1)
  have hn : tail + 1 + block = n := by
    dsimp [tail]
    omega
  have hf := quaternionHaar_partialHaarHeads (tail + 1) block
    (angularDerivative (4 * block + i) (4 * block + j) polynomial)
  rw [hn] at hf
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm hf) ?_
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff
      (angularDerivative_partialHaarHeads block i j polynomial).symm) ?_
  exact quaternionHaar_angularDerivative_zero tail hi hj
    (partialHaarHeads block polynomial)

/-- Exact weighted angular integration by parts in any in-range quaternion
block.  Both product-rule terms are retained, with arbitrary signed
polynomials and no support or positivity hypothesis. -/
theorem quaternionHaar_weighted_angular_at
    {n block i j : Nat} (hblock : block < n) (hi : i < 4) (hj : j < 4)
    (weight test : RatPoly) :
    quaternionHaar n
      (polyAdd
        (polyMul (angularDerivative (4 * block + i) (4 * block + j) weight) test)
        (polyMul weight
          (angularDerivative (4 * block + i) (4 * block + j) test))) ≈ 0 := by
  refine Q'.eqv_trans _ _ _
    (haar_of_coeff
      (angularDerivative_mul (4 * block + i) (4 * block + j) weight test).symm) ?_
  exact quaternionHaar_angularDerivative_at hblock hi hj (polyMul weight test)

private theorem neg_of_sum_zero (a b : Q') (h : a + b ≈ 0) : b ≈ -a := by
  apply QPoly.q_eqv_of_sub_zero
  exact Q'.eqv_trans _ _ _
    (poly_identity_of_normal_eq (.add (.var 0) (.neg (.neg (.var 1))))
      (.add (.var 1) (.var 0)) (by decide) (fun n => if n = 0 then b else a)) h

/-- Arbitrary-block skew-adjointness of the angular vector field on the
original product Haar carrier. -/
theorem angular_pair_at
    {n block i j : Nat} (hblock : block < n) (hi : i < 4) (hj : j < 4)
    (insertion polynomial : RatPoly) :
    quaternionHaar n
        (polyMul insertion
          (angularDerivative (4 * block + i) (4 * block + j) polynomial)) ≈
      -(quaternionHaar n
        (polyMul (angularDerivative (4 * block + i) (4 * block + j) insertion)
          polynomial)) :=
  neg_of_sum_zero _ _ (Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_append n _ _))
    (quaternionHaar_weighted_angular_at hblock hi hj insertion polynomial))

/-- Tangential differentiation in any in-range block preserves equality
under every insertion in the same original Haar carrier. -/
theorem angularDerivative_carrier_at
    {blocks block i j : Nat} {p q : RatPoly}
    (hblock : block < blocks) (hi : i < 4) (hj : j < 4)
    (h : HaarCarrierEqv blocks p q) :
    HaarCarrierEqv blocks
      (angularDerivative (4 * block + i) (4 * block + j) p)
      (angularDerivative (4 * block + i) (4 * block + j) q) := by
  intro insertion
  exact Q'.eqv_trans _ _ _ (angular_pair_at hblock hi hj insertion p)
    (Q'.eqv_trans _ _ _
      (Q'.neg_eqv_congr _ _
        (h (angularDerivative (4 * block + i) (4 * block + j) insertion)))
      (Q'.eqv_symm (angular_pair_at hblock hi hj insertion q)))

end YMGap.Continuum.SU2QuaternionHaarAngularIBPAt

#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.quaternionHaar_angularDerivative_at
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.quaternionHaar_weighted_angular_at
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.partialHaarHeads_angularDerivative_at_zero
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.angular_pair_at
#print axioms YMGap.Continuum.SU2QuaternionHaarAngularIBPAt.angularDerivative_carrier_at
