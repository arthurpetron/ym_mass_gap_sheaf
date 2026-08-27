/-
# Composition and tensor product of finite bistochastic kernels

Sequential recoupling is matrix multiplication, not a dependent path-space
row.  Independent crossed replicas are tensor products.  This module proves
constructively that both operations preserve exact row and column mass.

Constructive contract: finite lists and exact `Q'` algebra only; no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernel
import YMGap.Continuum.FiniteDeterministicKernelPushforward
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.FiniteBistochasticQKernelComposition

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Sequential matrix multiplication -/

/-- Matrix product through the first kernel's explicit target carrier. -/
def composedWeight {A B C : Type}
    (first : FiniteBistochasticQKernel A B)
    (second : FiniteBistochasticQKernel B C)
    (source : A) (target : C) : Q' :=
  listQSum
    (fun middle => first.weight source middle * second.weight middle target)
    first.targets

theorem composedWeight_nonnegative {A B C : Type}
    (first : FiniteBistochasticQKernel A B)
    (second : FiniteBistochasticQKernel B C)
    (source : A) (target : C) :
    (0 : Q') ≤ composedWeight first second source target := by
  unfold composedWeight
  apply listQSum_nonnegative_on
  intro middle _
  exact Q'.mul_nonneg _ _
    (first.weight_nonnegative source middle)
    (second.weight_nonnegative middle target)

private theorem composed_row_normalized {A B C : Type}
    (first : FiniteBistochasticQKernel A B)
    (second : FiniteBistochasticQKernel B C)
    (source : A) :
    listQSum (composedWeight first second source) second.targets ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun middle => listQSum
        (fun target => first.weight source middle *
          second.weight middle target)
        second.targets)
      first.targets) _ ?_ ?_
  · exact listQSum_swap
      (fun middle target => first.weight source middle *
        second.weight middle target)
      first.targets second.targets
  · refine Q'.eqv_trans _
      (listQSum (fun middle => first.weight source middle * 1)
        first.targets) _ ?_ ?_
    · apply listQSum_congr
      intro middle
      exact Q'.eqv_trans _
        (first.weight source middle *
          listQSum (second.weight middle) second.targets) _
        (listQSum_mul_left (first.weight source middle)
          (second.weight middle) second.targets)
        (Q'.mul_eqv_congr_left (first.weight source middle) _ _
          (second.row_normalized middle))
    · exact Q'.eqv_trans _
        (listQSum (first.weight source) first.targets) _
        (listQSum_congr
          (fun middle => Q'.mul_one_eqv (first.weight source middle))
          first.targets)
        (first.row_normalized source)

private theorem composed_column_normalized {A B C : Type}
    (first : FiniteBistochasticQKernel A B)
    (second : FiniteBistochasticQKernel B C)
    (hmiddle : first.targets = second.sources)
    (target : C) :
    listQSum (fun source => composedWeight first second source target)
      first.sources ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun middle => listQSum
        (fun source => first.weight source middle *
          second.weight middle target)
        first.sources)
      first.targets) _ ?_ ?_
  · exact Q'.eqv_symm (by
      simpa only [composedWeight] using
        (listQSum_swap
          (fun source middle => first.weight source middle *
            second.weight middle target)
          first.sources first.targets))
  · refine Q'.eqv_trans _
      (listQSum (fun middle => second.weight middle target)
        first.targets) _ ?_ ?_
    · apply listQSum_congr
      intro middle
      refine Q'.eqv_trans _
        (second.weight middle target *
          listQSum (fun source => first.weight source middle)
            first.sources) _ ?_ ?_
      · refine Q'.eqv_trans _
          (listQSum
            (fun source => second.weight middle target *
              first.weight source middle)
            first.sources) _ ?_ ?_
        · apply listQSum_congr
          intro source
          exact Q'.mul_comm_eqv _ _
        · exact listQSum_mul_left (second.weight middle target)
            (fun source => first.weight source middle) first.sources
      · exact Q'.eqv_trans _ (second.weight middle target * 1) _
          (Q'.mul_eqv_congr_left (second.weight middle target) _ _
            (first.column_normalized middle))
          (Q'.mul_one_eqv _)
    · rw [hmiddle]
      exact second.column_normalized target

/-- **Exact finite bistochastic kernels are closed under sequential
composition whenever the two written middle carriers agree.** -/
def compose {A B C : Type}
    (first : FiniteBistochasticQKernel A B)
    (second : FiniteBistochasticQKernel B C)
    (hmiddle : first.targets = second.sources) :
    FiniteBistochasticQKernel A C where
  sources := first.sources
  targets := second.targets
  weight := composedWeight first second
  weight_nonnegative := composedWeight_nonnegative first second
  row_normalized := composed_row_normalized first second
  column_normalized := composed_column_normalized first second hmiddle

/-! ## 2. Independent Cartesian tensor products -/

/-- Product entry for two independent finite kernels. -/
def tensorWeight {A B C D : Type}
    (left : FiniteBistochasticQKernel A B)
    (right : FiniteBistochasticQKernel C D)
    (source : A × C) (target : B × D) : Q' :=
  left.weight source.1 target.1 * right.weight source.2 target.2

theorem tensorWeight_nonnegative {A B C D : Type}
    (left : FiniteBistochasticQKernel A B)
    (right : FiniteBistochasticQKernel C D)
    (source : A × C) (target : B × D) :
    (0 : Q') ≤ tensorWeight left right source target := by
  exact Q'.mul_nonneg _ _
    (left.weight_nonnegative source.1 target.1)
    (right.weight_nonnegative source.2 target.2)

private theorem tensor_row_normalized {A B C D : Type}
    (left : FiniteBistochasticQKernel A B)
    (right : FiniteBistochasticQKernel C D)
    (source : A × C) :
    listQSum (tensorWeight left right source)
      (cartesian left.targets right.targets) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (left.weight source.1) left.targets *
      listQSum (right.weight source.2) right.targets) _ ?_ ?_
  · exact listQSum_cartesian_product
      (left.weight source.1) (right.weight source.2)
      left.targets right.targets
  · refine Q'.eqv_trans _
      (1 * listQSum (right.weight source.2) right.targets) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (left.row_normalized source.1)
    · exact Q'.eqv_trans _ (1 * 1) _
        (Q'.mul_eqv_congr_left 1 _ _
          (right.row_normalized source.2))
        (Q'.one_mul_eqv 1)

private theorem tensor_column_normalized {A B C D : Type}
    (left : FiniteBistochasticQKernel A B)
    (right : FiniteBistochasticQKernel C D)
    (target : B × D) :
    listQSum (fun source => tensorWeight left right source target)
      (cartesian left.sources right.sources) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum (fun source => left.weight source target.1) left.sources *
      listQSum (fun source => right.weight source target.2) right.sources) _
    (listQSum_cartesian_product
      (fun source => left.weight source target.1)
      (fun source => right.weight source target.2)
      left.sources right.sources) ?_
  refine Q'.eqv_trans _
    (1 * listQSum (fun source => right.weight source target.2)
      right.sources) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (left.column_normalized target.1)
  · exact Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left 1 _ _
        (right.column_normalized target.2))
      (Q'.one_mul_eqv 1)

/-- **Independent Cartesian products of finite bistochastic kernels remain
bistochastic on the literal product carriers.** -/
def tensor {A B C D : Type}
    (left : FiniteBistochasticQKernel A B)
    (right : FiniteBistochasticQKernel C D) :
    FiniteBistochasticQKernel (A × C) (B × D) where
  sources := cartesian left.sources right.sources
  targets := cartesian left.targets right.targets
  weight := tensorWeight left right
  weight_nonnegative := tensorWeight_nonnegative left right
  row_normalized := tensor_row_normalized left right
  column_normalized := tensor_column_normalized left right

end YMGap.Continuum.FiniteBistochasticQKernelComposition

#print axioms YMGap.Continuum.FiniteBistochasticQKernelComposition.composedWeight_nonnegative
#print axioms YMGap.Continuum.FiniteBistochasticQKernelComposition.compose
#print axioms YMGap.Continuum.FiniteBistochasticQKernelComposition.tensorWeight_nonnegative
#print axioms YMGap.Continuum.FiniteBistochasticQKernelComposition.tensor
