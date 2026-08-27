/-
# Constructive heterogeneous products of finite bistochastic kernels

Different slab links have different source and target carrier types.  This
module packages each finite bistochastic matrix with its carrier types and
forms their dependent finite product.  A source and a target assignment keep
one correctly typed coordinate for every matrix in the written list, and the
global entry is the product of the local entries.

Exact row and column normalization follow from the same finite Fubini
argument.  No cardinality identification or choice of a common ambient
carrier is used.

Constructive contract: exact `Q'`, dependent finite lists, no choice,
`Classical`, `sorry`, or new axiom.
-/

import YMGap.Continuum.FiniteBistochasticQKernelComposition

namespace YMGap.Continuum.FiniteBistochasticQKernelProduct

open YMGap.Constructive
open YMGap.Continuum.FiniteBistochasticQKernel
open YMGap.Continuum.FiniteBistochasticQKernelComposition
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Type-erased only at the package boundary -/

/-- One finite bistochastic matrix together with its actual source and target
types. -/
structure FiniteBistochasticQKernelPackage where
  Source : Type
  Target : Type
  kernel : FiniteBistochasticQKernel Source Target

/-- A packaged matrix together with one distinguished source row. -/
structure PointedFiniteBistochasticQKernelPackage where
  package : FiniteBistochasticQKernelPackage
  source : package.Source

/-- Forget the distinguished rows while retaining the exact dependent
carrier types. -/
def finiteBistochasticPackagesOfPointed :
    List PointedFiniteBistochasticQKernelPackage →
      List FiniteBistochasticQKernelPackage
  | [] => []
  | pointed :: points =>
      pointed.package :: finiteBistochasticPackagesOfPointed points

/-- One correctly typed source coordinate for every packaged matrix. -/
def FiniteBistochasticSourceAssignment :
    List FiniteBistochasticQKernelPackage → Type
  | [] => Unit
  | package :: packages =>
      package.Source × FiniteBistochasticSourceAssignment packages

/-- One correctly typed target coordinate for every packaged matrix. -/
def FiniteBistochasticTargetAssignment :
    List FiniteBistochasticQKernelPackage → Type
  | [] => Unit
  | package :: packages =>
      package.Target × FiniteBistochasticTargetAssignment packages

/-- Explicit enumeration of all heterogeneous source assignments. -/
def finiteBistochasticSourceAssignments :
    (packages : List FiniteBistochasticQKernelPackage) →
      List (FiniteBistochasticSourceAssignment packages)
  | [] => [()]
  | package :: packages =>
      package.kernel.sources.flatMap fun source =>
        (finiteBistochasticSourceAssignments packages).map fun tail =>
          (source, tail)

/-- Explicit enumeration of all heterogeneous target assignments. -/
def finiteBistochasticTargetAssignments :
    (packages : List FiniteBistochasticQKernelPackage) →
      List (FiniteBistochasticTargetAssignment packages)
  | [] => [()]
  | package :: packages =>
      package.kernel.targets.flatMap fun target =>
        (finiteBistochasticTargetAssignments packages).map fun tail =>
          (target, tail)

/-- Product of the selected local matrix entries. -/
def finiteBistochasticProductWeight :
    {packages : List FiniteBistochasticQKernelPackage} →
      FiniteBistochasticSourceAssignment packages →
      FiniteBistochasticTargetAssignment packages → Q'
  | [], _, _ => 1
  | package :: _, source, target =>
      package.kernel.weight source.1 target.1 *
        finiteBistochasticProductWeight source.2 target.2

/-- The explicit global source obtained by taking every distinguished local
row in written order. -/
def pointedFiniteBistochasticSourceAssignment :
    (points : List PointedFiniteBistochasticQKernelPackage) →
      FiniteBistochasticSourceAssignment
        (finiteBistochasticPackagesOfPointed points)
  | [] => ()
  | pointed :: points =>
      (pointed.source, pointedFiniteBistochasticSourceAssignment points)

theorem finiteBistochasticProductWeight_nonnegative :
    {packages : List FiniteBistochasticQKernelPackage} →
      (source : FiniteBistochasticSourceAssignment packages) →
      (target : FiniteBistochasticTargetAssignment packages) →
      (0 : Q') ≤ finiteBistochasticProductWeight source target
  | [], _, _ => Q'.zero_le_one
  | package :: packages, source, target => by
      exact Q'.mul_nonneg _ _
        (package.kernel.weight_nonnegative source.1 target.1)
        (finiteBistochasticProductWeight_nonnegative source.2 target.2)

/-! ## 2. Exact row and column finite Fubini -/

theorem finiteBistochasticProduct_row_normalized :
    (packages : List FiniteBistochasticQKernelPackage) →
    (source : FiniteBistochasticSourceAssignment packages) →
      listQSum (finiteBistochasticProductWeight source)
          (finiteBistochasticTargetAssignments packages) ≈ 1
  | [], _ => Q'.eqv_of_eq (Q'.add_zero' 1)
  | package :: packages, source => by
      refine Q'.eqv_trans _
        (listQSum
          (fun target =>
            listQSum
              (@finiteBistochasticProductWeight (package :: packages)
                source)
              ((finiteBistochasticTargetAssignments packages).map fun tail =>
                ((target, tail) :
                  FiniteBistochasticTargetAssignment
                    (package :: packages))))
          package.kernel.targets) _
        (listQSum_flatMap
          (@finiteBistochasticProductWeight (package :: packages) source)
          (fun target =>
            (finiteBistochasticTargetAssignments packages).map fun tail =>
              ((target, tail) :
                FiniteBistochasticTargetAssignment (package :: packages)))
          package.kernel.targets) ?_
      refine Q'.eqv_trans _
        (listQSum (package.kernel.weight source.1)
          package.kernel.targets) _
        (listQSum_congr (fun target => ?_) package.kernel.targets)
        (package.kernel.row_normalized source.1)
      rw [listQSum_map]
      change listQSum
          (fun tail => package.kernel.weight source.1 target *
            finiteBistochasticProductWeight source.2 tail)
          (finiteBistochasticTargetAssignments packages) ≈
        package.kernel.weight source.1 target
      refine Q'.eqv_trans _
        (package.kernel.weight source.1 target *
          listQSum (finiteBistochasticProductWeight source.2)
            (finiteBistochasticTargetAssignments packages)) _
        (listQSum_mul_left (package.kernel.weight source.1 target)
          (finiteBistochasticProductWeight source.2)
          (finiteBistochasticTargetAssignments packages)) ?_
      exact Q'.eqv_trans _
        (package.kernel.weight source.1 target * 1) _
        (Q'.mul_eqv_congr_left _ _ _
          (finiteBistochasticProduct_row_normalized packages source.2))
        (Q'.mul_one_eqv _)

theorem finiteBistochasticProduct_column_normalized :
    (packages : List FiniteBistochasticQKernelPackage) →
    (target : FiniteBistochasticTargetAssignment packages) →
      listQSum
          (fun source => finiteBistochasticProductWeight source target)
          (finiteBistochasticSourceAssignments packages) ≈ 1
  | [], _ => Q'.eqv_of_eq (Q'.add_zero' 1)
  | package :: packages, target => by
      refine Q'.eqv_trans _
        (listQSum
          (fun source =>
            listQSum
              (fun fullSource =>
                @finiteBistochasticProductWeight (package :: packages)
                  fullSource target)
              ((finiteBistochasticSourceAssignments packages).map fun tail =>
                ((source, tail) :
                  FiniteBistochasticSourceAssignment
                    (package :: packages))))
          package.kernel.sources) _
        (listQSum_flatMap
          (fun source =>
            @finiteBistochasticProductWeight (package :: packages)
              source target)
          (fun source =>
            (finiteBistochasticSourceAssignments packages).map fun tail =>
              ((source, tail) :
                FiniteBistochasticSourceAssignment (package :: packages)))
          package.kernel.sources) ?_
      refine Q'.eqv_trans _
        (listQSum (fun source => package.kernel.weight source target.1)
          package.kernel.sources) _
        (listQSum_congr (fun source => ?_) package.kernel.sources)
        (package.kernel.column_normalized target.1)
      rw [listQSum_map]
      change listQSum
          (fun tail => package.kernel.weight source target.1 *
            finiteBistochasticProductWeight tail target.2)
          (finiteBistochasticSourceAssignments packages) ≈
        package.kernel.weight source target.1
      refine Q'.eqv_trans _
        (package.kernel.weight source target.1 *
          listQSum
            (fun tail => finiteBistochasticProductWeight tail target.2)
            (finiteBistochasticSourceAssignments packages)) _
        (listQSum_mul_left (package.kernel.weight source target.1)
          (fun tail => finiteBistochasticProductWeight tail target.2)
          (finiteBistochasticSourceAssignments packages)) ?_
      exact Q'.eqv_trans _
        (package.kernel.weight source target.1 * 1) _
        (Q'.mul_eqv_congr_left _ _ _
          (finiteBistochasticProduct_column_normalized packages target.2))
        (Q'.mul_one_eqv _)

/-! ## 3. The packaged global matrix -/

/-- **A finite heterogeneous product of finite bistochastic matrices is one
finite bistochastic matrix on the exact dependent product carriers.** -/
def finiteBistochasticKernelProduct
    (packages : List FiniteBistochasticQKernelPackage) :
    FiniteBistochasticQKernel
      (FiniteBistochasticSourceAssignment packages)
      (FiniteBistochasticTargetAssignment packages) where
  sources := finiteBistochasticSourceAssignments packages
  targets := finiteBistochasticTargetAssignments packages
  weight := finiteBistochasticProductWeight
  weight_nonnegative := finiteBistochasticProductWeight_nonnegative
  row_normalized := finiteBistochasticProduct_row_normalized packages
  column_normalized := finiteBistochasticProduct_column_normalized packages

end YMGap.Continuum.FiniteBistochasticQKernelProduct

#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticSourceAssignments
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticTargetAssignments
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticProductWeight
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.pointedFiniteBistochasticSourceAssignment
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticProductWeight_nonnegative
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticProduct_row_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticProduct_column_normalized
#print axioms YMGap.Continuum.FiniteBistochasticQKernelProduct.finiteBistochasticKernelProduct
