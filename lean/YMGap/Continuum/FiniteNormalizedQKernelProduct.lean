/-
# Constructive dependent products of finite normalized rational kernels

A slab link can carry a recoupling row whose target type depends on the
link's actual valence.  An ordinary Cartesian power therefore erases exactly
the typing information that the local compiler established.  This module
forms the heterogeneous finite product directly: an assignment chooses one
target from each kernel in a list, and its weight is the product of the local
weights.

The assignment list is explicit and finite.  Exact normalization is proved by
structural finite Fubini, not by choice or a generic measure-theory layer.

Constructive contract: exact `Q'`, dependent inductive assignments, finite
lists, no `Classical`, no choice, no `sorry`, and no new axiom.
-/

import YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel

namespace YMGap.Continuum.FiniteNormalizedQKernelProduct

open YMGap.Constructive
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabAllValenceCrossedSchurKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The typed global target carrier -/

/-- A heterogeneous target choice, with one entry in the internal target type
of every kernel in the indexed list. -/
def FiniteKernelAssignment :
    List FiniteNormalizedQKernel → Type
  | [] => Unit
  | kernel :: kernels => kernel.Target × FiniteKernelAssignment kernels

/-- Explicit enumeration of all heterogeneous target choices. -/
def finiteKernelAssignments :
  (kernels : List FiniteNormalizedQKernel) →
      List (FiniteKernelAssignment kernels)
  | [] => [()]
  | kernel :: kernels =>
      kernel.targets.flatMap fun target =>
        (finiteKernelAssignments kernels).map fun tail =>
          (target, tail)

/-- Product of the selected local weights. -/
def finiteKernelAssignmentWeight :
    {kernels : List FiniteNormalizedQKernel} →
      FiniteKernelAssignment kernels → Q'
  | [], _ => 1
  | kernel :: _, assignment =>
      kernel.weight assignment.1 *
        finiteKernelAssignmentWeight assignment.2

/-! ## 2. Exact finite-product algebra -/

private theorem listQSum_mul_left_product {A : Type}
    (a : Q') (weight : A → Q') : ∀ items : List A,
    listQSum (fun item => a * weight item) items ≈
      a * listQSum weight items
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv a)
  | item :: items => by
      change a * weight item +
          listQSum (fun next => a * weight next) items ≈
        a * (weight item + listQSum weight items)
      exact Q'.eqv_trans _
        (a * weight item + a * listQSum weight items) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_left_product a weight items))
        (Q'.eqv_symm (Q'.mul_add_eqv a _ _))

theorem finiteKernelAssignmentWeight_nonnegative :
    {kernels : List FiniteNormalizedQKernel} →
      (assignment : FiniteKernelAssignment kernels) →
        (0 : Q') ≤ finiteKernelAssignmentWeight assignment
  | [], _ => Q'.zero_le_one
  | kernel :: kernels, assignment => by
      exact Q'.mul_nonneg _ _
        (kernel.weight_nonnegative assignment.1)
        (finiteKernelAssignmentWeight_nonnegative assignment.2)

/-- **A finite heterogeneous product of exact normalized rows is itself an
exact normalized row.** -/
theorem finiteKernelProduct_row_normalized :
    (kernels : List FiniteNormalizedQKernel) →
      listQSum finiteKernelAssignmentWeight
          (finiteKernelAssignments kernels) ≈ 1
  | [] => Q'.eqv_of_eq (Q'.add_zero' 1)
  | kernel :: kernels => by
      refine Q'.eqv_trans _
        (listQSum
          (fun target =>
            listQSum (@finiteKernelAssignmentWeight (kernel :: kernels))
              ((finiteKernelAssignments kernels).map fun tail =>
                ((target, tail) :
                  FiniteKernelAssignment (kernel :: kernels))))
          kernel.targets) _
        (listQSum_flatMap
          (@finiteKernelAssignmentWeight (kernel :: kernels))
          (fun target =>
            (finiteKernelAssignments kernels).map fun tail =>
              ((target, tail) :
                FiniteKernelAssignment (kernel :: kernels)))
          kernel.targets) ?_
      refine Q'.eqv_trans _ (listQSum kernel.weight kernel.targets) _
        (listQSum_congr (fun target => ?_) kernel.targets)
        kernel.row_normalized
      rw [listQSum_map]
      change listQSum
          (fun tail => kernel.weight target *
            finiteKernelAssignmentWeight tail)
          (finiteKernelAssignments kernels) ≈ kernel.weight target
      refine Q'.eqv_trans _
        (kernel.weight target *
          listQSum finiteKernelAssignmentWeight
            (finiteKernelAssignments kernels)) _
        (listQSum_mul_left_product (kernel.weight target)
          finiteKernelAssignmentWeight
          (finiteKernelAssignments kernels)) ?_
      exact Q'.eqv_trans _ (kernel.weight target * 1) _
        (Q'.mul_eqv_congr_left (kernel.weight target) _ _
          (finiteKernelProduct_row_normalized kernels))
        (Q'.mul_one_eqv (kernel.weight target))

/-! ## 3. Constant-observable preservation -/

def finiteKernelProductExpectation
    (kernels : List FiniteNormalizedQKernel)
    (observable : FiniteKernelAssignment kernels → Q') : Q' :=
  listQSum
    (fun assignment => finiteKernelAssignmentWeight assignment *
      observable assignment)
    (finiteKernelAssignments kernels)

theorem finiteKernelProductExpectation_one
    (kernels : List FiniteNormalizedQKernel) :
    finiteKernelProductExpectation kernels (fun _ => 1) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum finiteKernelAssignmentWeight
      (finiteKernelAssignments kernels)) _
    (listQSum_congr
      (fun assignment => Q'.mul_one_eqv
        (finiteKernelAssignmentWeight assignment))
      (finiteKernelAssignments kernels))
    (finiteKernelProduct_row_normalized kernels)

#print axioms finiteKernelAssignments
#print axioms finiteKernelAssignmentWeight
#print axioms finiteKernelAssignmentWeight_nonnegative
#print axioms finiteKernelProduct_row_normalized
#print axioms finiteKernelProductExpectation_one

end YMGap.Continuum.FiniteNormalizedQKernelProduct
