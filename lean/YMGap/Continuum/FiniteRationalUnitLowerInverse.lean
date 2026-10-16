/-
# Constructive inverse of finite unit-lower rational matrices

This module gives the recursive block inverse of a finite unit-lower matrix.
The head column is arbitrary and the tail inverse is supplied as explicit
data.  Both multiplication orders are proved entrywise using only finite
rational sums and the checked matrix associativity theorem.

The immediate consumer is the positive-LDL producer.  No determinant,
classical finite-dimensional argument, Gaussian law, continuum limit, or
mass-gap statement is used here.
-/

import YMGap.Continuum.FiniteRationalMatrixAlgebra

namespace YMGap.Continuum.FiniteRationalUnitLowerInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

/-- Add a unit head row and an arbitrary first column to a unit-lower tail. -/
def prependUnitLower
    (headColumn : Nat → Q') (tail : Nat → Nat → Q') :
    Nat → Nat → Q'
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | row + 1, 0 => headColumn row
  | row + 1, column + 1 => tail row column

/-- Apply a finite matrix to a finite column vector. -/
def finiteMatrixVectorApply
    (n : Nat) (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (row : Nat) : Q' :=
  listQSum (fun column => matrix row column * vector column) (List.range n)

/-- Lower-left block in the recursive inverse. -/
def unitLowerInverseHead
    (n : Nat) (tailInverse : Nat → Nat → Q')
    (headColumn : Nat → Q') (row : Nat) : Q' :=
  -(finiteMatrixVectorApply n tailInverse headColumn row)

/-- Recursive block inverse candidate for `prependUnitLower`. -/
def prependUnitLowerInverse
    (n : Nat) (headColumn : Nat → Q')
    (tailInverse : Nat → Nat → Q') : Nat → Nat → Q' :=
  prependUnitLower (unitLowerInverseHead n tailInverse headColumn) tailInverse

/-- Entrywise shape of a finite unit-lower matrix. -/
def IsUnitLower
    (n : Nat) (matrix : Nat → Nat → Q') : Prop :=
  (∀ {index : Nat}, index < n → matrix index index = 1) ∧
    (∀ {row column : Nat}, row < n → column < n → row < column →
      matrix row column = 0)

/-- The empty matrix is unit-lower. -/
theorem isUnitLower_zero (matrix : Nat → Nat → Q') :
    IsUnitLower 0 matrix := by
  constructor <;> intro <;> omega

/-- Prepending a unit head row preserves unit-lower shape. -/
theorem prependUnitLower_isUnitLower
    {n : Nat} (headColumn : Nat → Q') (tail : Nat → Nat → Q')
    (htail : IsUnitLower n tail) :
    IsUnitLower (n + 1) (prependUnitLower headColumn tail) := by
  constructor
  · intro index hindex
    cases index with
    | zero => rfl
    | succ index =>
        exact htail.1 (by omega)
  · intro row column hrow hcolumn hlt
    cases row with
    | zero =>
        cases column with
        | zero => omega
        | succ column => rfl
    | succ row =>
        cases column with
        | zero => omega
        | succ column =>
            exact htail.2 (by omega) (by omega) (by omega)

/-- The recursive inverse candidate has the same unit-lower shape as the
supplied tail inverse. -/
theorem prependUnitLowerInverse_isUnitLower
    {n : Nat} (headColumn : Nat → Q') (tailInverse : Nat → Nat → Q')
    (htail : IsUnitLower n tailInverse) :
    IsUnitLower (n + 1)
      (prependUnitLowerInverse n headColumn tailInverse) := by
  unfold prependUnitLowerInverse
  exact prependUnitLower_isUnitLower _ _ htail

/-- Explicit two-sided inverse data for a finite unit-lower matrix. -/
structure UnitLowerInverseData
    (n : Nat) (lower : Nat → Nat → Q') : Type where
  inverse : Nat → Nat → Q'
  lower_inverse : FiniteMatrixEqv n
    (finiteMatrixProduct n lower inverse) finiteIdentityMatrix
  inverse_lower : FiniteMatrixEqv n
    (finiteMatrixProduct n inverse lower) finiteIdentityMatrix

namespace UnitLowerInverseData

/-- Vacuous inverse data in dimension zero. -/
def zero (lower : Nat → Nat → Q') : UnitLowerInverseData 0 lower where
  inverse := fun _ _ => 0
  lower_inverse := by intro row _column hrow; omega
  inverse_lower := by intro row _column hrow; omega

end UnitLowerInverseData

private theorem finiteMatrixProduct_succ_split
    (n : Nat) (left right : Nat → Nat → Q')
    (row column : Nat) :
    finiteMatrixProduct (n + 1) left right row column =
      left row 0 * right 0 column +
        listQSum
          (fun index => left row (index + 1) * right (index + 1) column)
          (List.range n) := by
  unfold finiteMatrixProduct
  rw [List.range_succ_eq_map]
  simp only [listQSum]
  rw [listQSum_map_local]

private theorem listQSum_prepend_top_zero
    (n : Nat) (headColumn : Nat → Q')
    (tail right : Nat → Nat → Q') (column : Nat) :
    listQSum
        (fun index =>
          prependUnitLower headColumn tail 0 (index + 1) *
            right (index + 1) column)
        (List.range n) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q')) (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    unfold prependUnitLower
    exact Q'.zero_mul_eqv _
  · exact listQSum_zero (List.range n)

private def repeatedColumn
    (vector : Nat → Q') (row _column : Nat) : Q' :=
  vector row

private theorem finiteMatrixVectorApply_eq_product
    (n : Nat) (matrix : Nat → Nat → Q')
    (vector : Nat → Q') (row column : Nat) :
    finiteMatrixVectorApply n matrix vector row =
      finiteMatrixProduct n matrix (repeatedColumn vector) row column := by
  unfold finiteMatrixVectorApply finiteMatrixProduct repeatedColumn
  rfl

private theorem tailLower_mul_inverseHead
    {n : Nat} {tailLower tailInverse : Nat → Nat → Q'}
    (headColumn : Nat → Q')
    (hlowerInverse : FiniteMatrixEqv n
      (finiteMatrixProduct n tailLower tailInverse) finiteIdentityMatrix)
    {row : Nat} (hrow : row < n) :
    listQSum
        (fun index =>
          tailLower row index *
            unitLowerInverseHead n tailInverse headColumn index)
        (List.range n) ≈
      -(headColumn row) := by
  have hzero : 0 < n := by omega
  have hassoc := finiteMatrixProduct_assoc n tailLower tailInverse
    (repeatedColumn headColumn) hrow hzero
  have hreplace := finiteMatrixProduct_congr hlowerInverse
    (finiteMatrixEqv_refl n (repeatedColumn headColumn)) hrow hzero
  have hidentity := finiteIdentityMatrix_mul n
    (repeatedColumn headColumn) hrow hzero
  have hpositive :
      listQSum
          (fun index => tailLower row index *
            finiteMatrixVectorApply n tailInverse headColumn index)
          (List.range n) ≈
        headColumn row := by
    change finiteMatrixProduct n tailLower
        (finiteMatrixProduct n tailInverse (repeatedColumn headColumn))
        row 0 ≈ headColumn row
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm hassoc)
      (Q'.eqv_trans _ _ _ hreplace (by
        simpa only [repeatedColumn] using hidentity))
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        -(tailLower row index *
          finiteMatrixVectorApply n tailInverse headColumn index))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    unfold unitLowerInverseHead
    exact Q'.mul_neg_eqv _ _
  · exact Q'.eqv_trans _ _ _
      (listQSum_neg_local
        (fun index => tailLower row index *
          finiteMatrixVectorApply n tailInverse headColumn index)
        (List.range n))
      (Q'.neg_eqv_congr _ _ hpositive)

/-- Prepending one arbitrary lower column preserves explicit two-sided
invertibility. -/
def prependUnitLowerInverseData
    {n : Nat} {tailLower : Nat → Nat → Q'}
    (headColumn : Nat → Q')
    (tail : UnitLowerInverseData n tailLower) :
    UnitLowerInverseData (n + 1) (prependUnitLower headColumn tailLower) where
  inverse := prependUnitLowerInverse n headColumn tail.inverse
  lower_inverse := by
    intro row column hrow hcolumn
    cases row with
    | zero =>
        cases column with
        | zero =>
            rw [finiteMatrixProduct_succ_split]
            refine Q'.eqv_trans _ (1 * 1 + 0) _ ?_ ?_
            · exact Q'.add_eqv_congr_left _ _ _
                (listQSum_prepend_top_zero n headColumn tailLower
                  (prependUnitLowerInverse n headColumn tail.inverse) 0)
            · exact Q'.eqv_trans _ (1 + 0) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1))
                (Q'.eqv_trans _ 1 _
                  (Q'.eqv_of_eq (Q'.add_zero' 1)) (Q'.eqv_refl _))
        | succ column =>
            rw [finiteMatrixProduct_succ_split]
            refine Q'.eqv_trans _ (1 * 0 + 0) _ ?_ ?_
            · exact Q'.add_eqv_congr_left _ _ _
                (listQSum_prepend_top_zero n headColumn tailLower
                  (prependUnitLowerInverse n headColumn tail.inverse)
                  (column + 1))
            · unfold finiteIdentityMatrix
              rw [if_neg (by omega)]
              exact Q'.eqv_trans _ (0 + 0) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv 0))
                (Q'.eqv_of_eq (Q'.zero_add' 0))
    | succ row =>
        have hrowTail : row < n := by omega
        cases column with
        | zero =>
            rw [finiteMatrixProduct_succ_split]
            change headColumn row * 1 +
                listQSum
                  (fun index => tailLower row index *
                    unitLowerInverseHead n tail.inverse headColumn index)
                  (List.range n) ≈ finiteIdentityMatrix (row + 1) 0
            unfold finiteIdentityMatrix
            rw [if_neg (by omega)]
            exact Q'.eqv_trans _
              (headColumn row + -(headColumn row)) _
              (Q'.add_eqv_congr'
                (Q'.mul_one_eqv _)
                (tailLower_mul_inverseHead headColumn
                  tail.lower_inverse hrowTail))
              (Q'.add_neg_self_eqv _)
        | succ column =>
            have hcolumnTail : column < n := by omega
            rw [finiteMatrixProduct_succ_split]
            change headColumn row * 0 +
                finiteMatrixProduct n tailLower tail.inverse row column ≈
              finiteIdentityMatrix (row + 1) (column + 1)
            refine Q'.eqv_trans _
              (finiteMatrixProduct n tailLower tail.inverse row column) _
              (Q'.eqv_trans _ (0 + _) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
                (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
            exact Q'.eqv_trans _ (finiteIdentityMatrix row column) _
              (tail.lower_inverse hrowTail hcolumnTail)
              (Q'.eqv_of_eq (by
                unfold finiteIdentityMatrix
                by_cases heq : row = column
                · subst column
                  rw [if_pos rfl, if_pos rfl]
                · have hsucc : row + 1 ≠ column + 1 := by omega
                  rw [if_neg heq, if_neg hsucc]))
  inverse_lower := by
    intro row column hrow hcolumn
    cases row with
    | zero =>
        cases column with
        | zero =>
            rw [finiteMatrixProduct_succ_split]
            refine Q'.eqv_trans _ (1 * 1 + 0) _ ?_ ?_
            · exact Q'.add_eqv_congr_left _ _ _
                (listQSum_prepend_top_zero n
                  (unitLowerInverseHead n tail.inverse headColumn)
                  tail.inverse (prependUnitLower headColumn tailLower) 0)
            · exact Q'.eqv_trans _ (1 + 0) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1))
                (Q'.eqv_trans _ 1 _
                  (Q'.eqv_of_eq (Q'.add_zero' 1)) (Q'.eqv_refl _))
        | succ column =>
            rw [finiteMatrixProduct_succ_split]
            refine Q'.eqv_trans _ (1 * 0 + 0) _ ?_ ?_
            · exact Q'.add_eqv_congr_left _ _ _
                (listQSum_prepend_top_zero n
                  (unitLowerInverseHead n tail.inverse headColumn)
                  tail.inverse (prependUnitLower headColumn tailLower)
                  (column + 1))
            · unfold finiteIdentityMatrix
              rw [if_neg (by omega)]
              exact Q'.eqv_trans _ (0 + 0) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.one_mul_eqv 0))
                (Q'.eqv_of_eq (Q'.zero_add' 0))
    | succ row =>
        have hrowTail : row < n := by omega
        cases column with
        | zero =>
            rw [finiteMatrixProduct_succ_split]
            change unitLowerInverseHead n tail.inverse headColumn row * 1 +
                finiteMatrixVectorApply n tail.inverse headColumn row ≈
              finiteIdentityMatrix (row + 1) 0
            unfold finiteIdentityMatrix unitLowerInverseHead
            rw [if_neg (by omega)]
            exact Q'.eqv_trans _
              (-(finiteMatrixVectorApply n tail.inverse headColumn row) +
                finiteMatrixVectorApply n tail.inverse headColumn row) _
              (Q'.add_eqv_congr_right _ _ _ (Q'.mul_one_eqv _))
              (Q'.neg_add_self_eqv _)
        | succ column =>
            have hcolumnTail : column < n := by omega
            rw [finiteMatrixProduct_succ_split]
            change unitLowerInverseHead n tail.inverse headColumn row * 0 +
                finiteMatrixProduct n tail.inverse tailLower row column ≈
              finiteIdentityMatrix (row + 1) (column + 1)
            refine Q'.eqv_trans _
              (finiteMatrixProduct n tail.inverse tailLower row column) _
              (Q'.eqv_trans _ (0 + _) _
                (Q'.add_eqv_congr_right _ _ _ (Q'.mul_zero_eqv _))
                (Q'.eqv_of_eq (Q'.zero_add' _))) ?_
            exact Q'.eqv_trans _ (finiteIdentityMatrix row column) _
              (tail.inverse_lower hrowTail hcolumnTail)
              (Q'.eqv_of_eq (by
                unfold finiteIdentityMatrix
                by_cases heq : row = column
                · subst column
                  rw [if_pos rfl, if_pos rfl]
                · have hsucc : row + 1 ≠ column + 1 := by omega
                  rw [if_neg heq, if_neg hsucc]))

end YMGap.Continuum.FiniteRationalUnitLowerInverse

#print axioms YMGap.Continuum.FiniteRationalUnitLowerInverse.tailLower_mul_inverseHead
#print axioms YMGap.Continuum.FiniteRationalUnitLowerInverse.prependUnitLower_isUnitLower
#print axioms YMGap.Continuum.FiniteRationalUnitLowerInverse.prependUnitLowerInverse_isUnitLower
#print axioms YMGap.Continuum.FiniteRationalUnitLowerInverse.prependUnitLowerInverseData
