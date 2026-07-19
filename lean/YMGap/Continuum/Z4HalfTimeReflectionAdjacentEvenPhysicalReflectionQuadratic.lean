/-
# The finite physical quadratic target for adjacent-even positivity

This leaf states the remaining one-step positivity problem on the exact finite
object that matters: the already-sandwiched physical reflected kernel indexed
by the enumerated lower half-states.  Indices outside the finite enumeration
are padded by zero, so the matrix is globally symmetric and admits the
repository's constructive `GramRep` interface without an arbitrary fallback
tail.

No Gram witness is postulated here.  The leaf proves only the exact matrix
support/symmetry facts and the constructive implication from an explicit Gram
witness to the required finite quadratic inequality.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.SchurHadamardTransfer
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Finite half-state indexing with a zero exterior -/

def adjacentEvenPhysicalHalfStateCount (K radius : Nat) : Nat :=
  (adjacentEvenHalfStates K radius).length

def adjacentEvenPhysicalHalfStateAt
    (K radius index : Nat) : EdgeLabelling :=
  (adjacentEvenHalfStates K radius).getD index zeroEdgeLabelling

private theorem list_getD_mem_of_lt {A : Type} (fallback : A) :
    forall (items : List A) (index : Nat), index < items.length ->
      items.getD index fallback ∈ items
  | [], index, hindex => absurd hindex (Nat.not_lt_zero index)
  | head :: tail, 0, _ => List.mem_cons_self
  | head :: tail, index + 1, hindex => by
      simp only [List.getD_cons_succ, List.mem_cons]
      apply Or.inr
      apply list_getD_mem_of_lt fallback tail index
      simp only [List.length_cons] at hindex
      omega

theorem adjacentEvenPhysicalHalfStateAt_mem
    {K radius index : Nat}
    (hindex : index < adjacentEvenPhysicalHalfStateCount K radius) :
    adjacentEvenPhysicalHalfStateAt K radius index ∈
      adjacentEvenHalfStates K radius := by
  exact list_getD_mem_of_lt zeroEdgeLabelling
    (adjacentEvenHalfStates K radius) index hindex

/-- The physical reflected matrix, padded by zero off the actual finite
half-state enumeration. -/
def adjacentEvenPhysicalReflectedMatrix
    (w : Q') (K radius left right : Nat) : Q' :=
  if left < adjacentEvenPhysicalHalfStateCount K radius then
    if right < adjacentEvenPhysicalHalfStateCount K radius then
      adjacentEvenPhysicalReflectedKernel w K radius
        (adjacentEvenPhysicalHalfStateAt K radius left)
        (adjacentEvenPhysicalHalfStateAt K radius right)
    else 0
  else 0

theorem adjacentEvenPhysicalReflectedMatrix_eq_kernel
    (w : Q') {K radius left right : Nat}
    (hleft : left < adjacentEvenPhysicalHalfStateCount K radius)
    (hright : right < adjacentEvenPhysicalHalfStateCount K radius) :
    adjacentEvenPhysicalReflectedMatrix w K radius left right =
      adjacentEvenPhysicalReflectedKernel w K radius
        (adjacentEvenPhysicalHalfStateAt K radius left)
        (adjacentEvenPhysicalHalfStateAt K radius right) := by
  simp [adjacentEvenPhysicalReflectedMatrix, hleft, hright]

/-- Exact global symmetry, including the zero-padded exterior. -/
theorem adjacentEvenPhysicalReflectedMatrix_symm
    (w : Q') (K radius left right : Nat) :
    adjacentEvenPhysicalReflectedMatrix w K radius left right ≈
      adjacentEvenPhysicalReflectedMatrix w K radius right left := by
  by_cases hleft : left < adjacentEvenPhysicalHalfStateCount K radius
  · by_cases hright : right < adjacentEvenPhysicalHalfStateCount K radius
    · rw [adjacentEvenPhysicalReflectedMatrix_eq_kernel w hleft hright,
        adjacentEvenPhysicalReflectedMatrix_eq_kernel w hright hleft]
      exact adjacentEvenPhysicalReflectedKernel_symm w
        (adjacentEvenPhysicalHalfStateAt_mem hleft)
        (adjacentEvenPhysicalHalfStateAt_mem hright)
    · simpa [adjacentEvenPhysicalReflectedMatrix, hleft, hright] using
        (Q'.eqv_refl (0 : Q'))
  · by_cases hright : right < adjacentEvenPhysicalHalfStateCount K radius
    · simpa [adjacentEvenPhysicalReflectedMatrix, hleft, hright] using
        (Q'.eqv_refl (0 : Q'))
    · simpa [adjacentEvenPhysicalReflectedMatrix, hleft, hright] using
        (Q'.eqv_refl (0 : Q'))

/-! ## 2. The exact finite PSD target -/

def adjacentEvenPhysicalReflectionQuadratic
    (w : Q') (K radius : Nat) (coefficient : Nat -> Q') : Q' :=
  gramQuadForm
    (adjacentEvenPhysicalReflectedMatrix w K radius)
    coefficient (adjacentEvenPhysicalHalfStateCount K radius)

/-- The minimal finite anchor-coupling positivity proposition.  This is the
statement downstream centered-limit and completion arguments consume. -/
def AdjacentEvenPhysicalAnchorPSD (K radius : Nat) : Prop :=
  forall coefficient : Nat -> Q',
    (0 : Q') <= adjacentEvenPhysicalReflectionQuadratic
      anchorCoupling K radius coefficient

/-- A constructive Gram witness for the exact zero-padded physical matrix.
This is a sufficient, Type-valued proof substrate, not part of the minimal
consumer proposition. -/
def AdjacentEvenPhysicalAnchorGramWitness (K radius : Nat) : Type :=
  GramRep
    (adjacentEvenPhysicalReflectedMatrix anchorCoupling K radius)

theorem adjacentEvenPhysicalReflectionQuadratic_anchor_nonnegative_of_gramRep
    (K radius : Nat)
    (rep : AdjacentEvenPhysicalAnchorGramWitness K radius)
    (coefficient : Nat -> Q') :
    (0 : Q') <= adjacentEvenPhysicalReflectionQuadratic
      anchorCoupling K radius coefficient := by
  exact gramPSD_quadForm_nonneg rep coefficient
    (adjacentEvenPhysicalHalfStateCount K radius)

theorem adjacentEvenPhysicalAnchorPSD_of_gramRep
    (K radius : Nat)
    (rep : AdjacentEvenPhysicalAnchorGramWitness K radius) :
    AdjacentEvenPhysicalAnchorPSD K radius := by
  intro coefficient
  exact adjacentEvenPhysicalReflectionQuadratic_anchor_nonnegative_of_gramRep
    K radius rep coefficient

#print axioms adjacentEvenPhysicalHalfStateAt_mem
#print axioms adjacentEvenPhysicalReflectedMatrix_eq_kernel
#print axioms adjacentEvenPhysicalReflectedMatrix_symm
#print axioms adjacentEvenPhysicalReflectionQuadratic_anchor_nonnegative_of_gramRep
#print axioms adjacentEvenPhysicalAnchorPSD_of_gramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalReflectionQuadratic
