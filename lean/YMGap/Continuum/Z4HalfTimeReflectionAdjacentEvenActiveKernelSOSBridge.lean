/-
# Entrywise reachable-kernel SOS bridge for adjacent-even positivity

The direct active-quadratic target is a finite weighted sum of squares in the
physical half-state coefficients.  A natural upstream certificate, produced
by the quaternion-polynomial/Haar construction, is instead entrywise: the
unscaled reachable fixed-interface matrix is a finite nonnegatively weighted
Gram kernel.

This leaf connects those two interfaces.  First it records the generic
`Nat`-indexed finite weighted Gram kernel and identifies its `gramQuadForm`
with the already defined `adjacentEvenActiveSOS`.  The proof reuses the
repository's constructive `GramRep.gramQuadForm_eq_sos` rearrangement; no
second finite-sum Fubini proof is introduced.  It then packages entrywise SOS
data for the reachable matrix and absorbs the exact physical outer scale into
each Gram coordinate.  The resulting data inhabit the minimal active
quadratic interface and hence transport mechanically to physical PSD.

The entrywise reachable certificate is intentionally Type-valued.  No
existence claim, square root, sign selection, classical reindexing, or
unbounded enumeration is used here.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveQuadraticSOSReduction

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveKernelSOSBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.HeatKernelGramSOS
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveQuadraticSOSReduction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableSandwichReduction
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableScaledQuadratic

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite weighted Gram kernel -/

/-- A `Nat`-indexed finite weighted Gram kernel.  The coordinate convention
matches `adjacentEvenActiveSOS`: `amplitude term state` is the coordinate of
`state` in the outer-product term `term`. -/
def finiteWeightedGramKernel
    (weight : Nat → Q') (amplitude : Nat → Nat → Q')
    (termCount left right : Nat) : Q' :=
  finSum (fun term =>
    weight term * (amplitude term left * amplitude term right)) termCount

/-- The generic finite weighted kernel is a constructive `GramRep` whenever
its stored weights are nonnegative. -/
def finiteWeightedGramKernelGramRep
    (weight : Nat → Q') (amplitude : Nat → Nat → Q')
    (termCount : Nat)
    (hweight : ∀ term, (0 : Q') ≤ weight term) :
    GramRep (finiteWeightedGramKernel weight amplitude termCount) where
  r := termCount
  d := weight
  hd := hweight
  v := amplitude
  hM := fun _ _ => Q'.eqv_refl _

/-- The `Nat`-finite quadratic form of the generic weighted Gram kernel is
exactly the manifest active SOS.  This is a direct specialization of the
existing constructive `gramQuadForm_eq_sos` theorem. -/
theorem finiteWeightedGramKernel_quadForm_eqv_activeSOS
    (weight : Nat → Q') (amplitude : Nat → Nat → Q')
    (coefficient : Nat → Q') (stateCount termCount : Nat)
    (hweight : ∀ term, (0 : Q') ≤ weight term) :
    gramQuadForm
        (finiteWeightedGramKernel weight amplitude termCount)
        coefficient stateCount ≈
      adjacentEvenActiveSOS
        weight amplitude coefficient stateCount termCount := by
  have hsos := gramQuadForm_eq_sos
    (finiteWeightedGramKernelGramRep
      weight amplitude termCount hweight)
    coefficient stateCount
  simpa [finiteWeightedGramKernelGramRep,
    adjacentEvenActiveSOS, adjacentEvenActiveSOSLinear] using hsos

/-! ## 2. Entrywise reachable-kernel certificate -/

/-- A finite weighted SOS factorization of the unscaled reachable
fixed-interface matrix.  This is the smallest entrywise target for the later
quaternion-polynomial/product-Haar construction: it supplies exactly the
weights, half-state coordinates, and matrix identity needed downstream. -/
structure AdjacentEvenReachableKernelSOSData
    (K radius : Nat) : Type where
  termCount : Nat
  weight : Nat → Q'
  weight_nonnegative : ∀ term, (0 : Q') ≤ weight term
  amplitude : Nat → Nat → Q'
  factorization : ∀ left right,
    adjacentEvenReachableFixedInterfaceMatrix K radius left right ≈
      finiteWeightedGramKernel weight amplitude termCount left right

/-- The entrywise certificate is, definitionally, a constructive Gram
witness for the unscaled reachable fixed-interface matrix. -/
def AdjacentEvenReachableKernelSOSData.toGramRep
    {K radius : Nat}
    (data : AdjacentEvenReachableKernelSOSData K radius) :
    AdjacentEvenReachableFixedInterfaceGramWitness K radius where
  r := data.termCount
  d := data.weight
  hd := data.weight_nonnegative
  v := data.amplitude
  hM := data.factorization

/-! ## 3. Absorb the physical outer scale and reach the active target -/

/-- An entrywise SOS of the unscaled reachable kernel supplies the exact
active-quadratic SOS after multiplying each half-state coordinate by the
physical outer factor.  The diagonal-congruence identity converts the scaled
coefficient vector to this coordinate scaling, and the existing generic
Gram-to-SOS theorem performs all finite-sum rearrangement. -/
def AdjacentEvenReachableKernelSOSData.toActiveQuadraticSOSData
    {K radius : Nat}
    (data : AdjacentEvenReachableKernelSOSData K radius) :
    AdjacentEvenActiveQuadraticSOSData K radius where
  termCount := data.termCount
  weight := data.weight
  weight_nonnegative := data.weight_nonnegative
  amplitude := fun term state =>
    adjacentEvenPhysicalOuterScale K radius state *
      data.amplitude term state
  factorization := by
    intro coefficient
    let stateCount := adjacentEvenPhysicalHalfStateCount K radius
    let outerScale := adjacentEvenPhysicalOuterScale K radius
    let scaledRep := diagonalKernelScaleGramRep data.toGramRep outerScale
    unfold adjacentEvenReachableScaledQuadratic
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (gramQuadForm_diagonalKernelScale_eqv
          (adjacentEvenReachableFixedInterfaceMatrix K radius)
          outerScale coefficient stateCount)) ?_
    have hsos := gramQuadForm_eq_sos scaledRep coefficient stateCount
    simpa [scaledRep, stateCount, outerScale,
      AdjacentEvenReachableKernelSOSData.toGramRep,
      diagonalKernelScaleGramRep,
      adjacentEvenActiveSOS, adjacentEvenActiveSOSLinear] using hsos

/-- The entrywise reachable-kernel certificate already contains everything
needed for positivity of the physically active scaled quadratic. -/
theorem AdjacentEvenReachableKernelSOSData.toReachableScaledPSD
    {K radius : Nat}
    (data : AdjacentEvenReachableKernelSOSData K radius) :
    AdjacentEvenReachableScaledPSD K radius :=
  data.toActiveQuadraticSOSData.toReachableScaledPSD

/-- **Entrywise reachable Gram implies physical adjacent-even positivity.**
All diagonal outer factors and Gram-to-quadratic rearrangements are absorbed
by the two checked bridge layers above. -/
theorem AdjacentEvenReachableKernelSOSData.toPhysicalPSD
    {K radius : Nat}
    (data : AdjacentEvenReachableKernelSOSData K radius) :
    AdjacentEvenPhysicalAnchorPSD K radius :=
  data.toActiveQuadraticSOSData.toPhysicalPSD

#print axioms finiteWeightedGramKernel_quadForm_eqv_activeSOS
#print axioms AdjacentEvenReachableKernelSOSData.toGramRep
#print axioms AdjacentEvenReachableKernelSOSData.toActiveQuadraticSOSData
#print axioms AdjacentEvenReachableKernelSOSData.toReachableScaledPSD
#print axioms AdjacentEvenReachableKernelSOSData.toPhysicalPSD

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenActiveKernelSOSBridge
