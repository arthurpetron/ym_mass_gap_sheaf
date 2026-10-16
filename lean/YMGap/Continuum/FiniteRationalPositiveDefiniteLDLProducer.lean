/-
# All-dimension constructive rational LDL producer

This module completes the recursive LDL construction for a finite symmetric
strictly positive rational matrix.  At each successor dimension it takes the
positive head pivot, forms the checked Schur pullback, recursively factors that
strictly positive symmetric tail, and prepends the head column.  The result is
Type-level exact data with strictly positive rational pivots, compiled by the
existing Boolean LDL checker.

No determinant choice, root selection, classical finite-dimensional algebra,
or external certificate oracle is used.  This module does not yet construct
the inverse from the LDL data or prove a Gaussian law, continuum limit, or
mass gap.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteSchur
import YMGap.Continuum.FiniteRationalUnitLowerInverse

namespace YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteSchur
open YMGap.Continuum.FiniteRationalUnitLowerInverse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

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

private theorem pivot_mul_entry_mul_recipPos_eqv
    (pivot entry : Q') (hpivot : (0 : Q') < pivot) :
    pivot * (entry * Q'.recipPos pivot hpivot) ≈ entry := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv pivot entry (Q'.recipPos pivot hpivot)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv pivot entry))
      (Q'.eqv_trans _ _ _
        (Q'.mul_assoc_eqv entry pivot (Q'.recipPos pivot hpivot))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left entry _ _
            (Q'.mul_recipPos_eqv pivot hpivot))
          (Q'.mul_one_eqv entry))))

private theorem add_cross_cancel_local (cross value : Q') :
    cross + (value + -cross) ≈ value := by
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv cross value (-cross)))
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_right _ _ _ (Q'.add_comm_eqv cross value))
      (Q'.eqv_trans _ _ _
        (Q'.add_assoc_eqv value cross (-cross))
        (Q'.eqv_trans _ (value + 0) _
          (Q'.add_eqv_congr_left value _ _
            (Q'.eqv_trans _ _ _
              (Q'.add_comm_eqv cross (-cross))
              (Q'.neg_add_self_eqv cross)))
          (Q'.eqv_of_eq (Q'.add_zero' value)))))

/-- Prepend the head column to an LDL lower factor. -/
def prependLower
    (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') : Nat → Nat → Q' :=
  prependUnitLower
    (fun row => matrix (row + 1) 0 * pivotInverse) tailLower

/-- Prepend the positive head pivot to the tail diagonal. -/
def prependDiagonal
    (matrix : Nat → Nat → Q') (tailDiagonal : Nat → Q') : Nat → Q'
  | 0 => matrix 0 0
  | index + 1 => tailDiagonal index

private theorem finiteLDLGram_prepend_split
    (n : Nat) (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (row column : Nat) :
    finiteLDLGram (n + 1)
        (prependLower matrix pivotInverse tailLower)
        (prependDiagonal matrix tailDiagonal) row column =
      prependDiagonal matrix tailDiagonal 0 *
          (prependLower matrix pivotInverse tailLower row 0 *
            prependLower matrix pivotInverse tailLower column 0) +
        listQSum
          (fun index =>
            prependDiagonal matrix tailDiagonal (index + 1) *
              (prependLower matrix pivotInverse tailLower row (index + 1) *
                prependLower matrix pivotInverse tailLower column (index + 1)))
          (List.range n) := by
  unfold finiteLDLGram
  rw [List.range_succ_eq_map]
  simp only [listQSum]
  rw [listQSum_map_local]

private theorem prepend_tail_zero_left
    (n : Nat) (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (column : Nat) :
    listQSum
        (fun index =>
          prependDiagonal matrix tailDiagonal (index + 1) *
            (prependLower matrix pivotInverse tailLower 0 (index + 1) *
              prependLower matrix pivotInverse tailLower column (index + 1)))
        (List.range n) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q')) (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    unfold prependLower
    exact Q'.eqv_trans _
      (prependDiagonal matrix tailDiagonal (index + 1) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv _))
      (Q'.mul_zero_eqv _)
  · exact listQSum_zero (List.range n)

private theorem prepend_tail_zero_right
    (n : Nat) (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (row : Nat) :
    listQSum
        (fun index =>
          prependDiagonal matrix tailDiagonal (index + 1) *
            (prependLower matrix pivotInverse tailLower row (index + 1) *
              prependLower matrix pivotInverse tailLower 0 (index + 1)))
        (List.range n) ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fun _index => (0 : Q')) (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    unfold prependLower
    exact Q'.eqv_trans _
      (prependDiagonal matrix tailDiagonal (index + 1) * 0) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_zero_eqv _))
      (Q'.mul_zero_eqv _)
  · exact listQSum_zero (List.range n)

private theorem finiteLDLGram_prepend_zero_zero
    (n : Nat) (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q') :
    finiteLDLGram (n + 1)
        (prependLower matrix pivotInverse tailLower)
        (prependDiagonal matrix tailDiagonal) 0 0 ≈
      matrix 0 0 := by
  rw [finiteLDLGram_prepend_split]
  refine Q'.eqv_trans _ (matrix 0 0 * (1 * 1) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (prepend_tail_zero_left n matrix pivotInverse
        tailLower tailDiagonal 0)
  · exact Q'.eqv_trans _ (matrix 0 0 * 1 + 0) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)))
      (Q'.eqv_trans _ (matrix 0 0 * 1) _
        (Q'.eqv_of_eq (Q'.add_zero' _))
        (Q'.mul_one_eqv _))

private theorem finiteLDLGram_prepend_zero_succ
    (n : Nat) (matrix : Nat → Nat → Q')
    (hpivot : (0 : Q') < matrix 0 0)
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (column : Nat) :
    finiteLDLGram (n + 1)
        (prependLower matrix (Q'.recipPos (matrix 0 0) hpivot) tailLower)
        (prependDiagonal matrix tailDiagonal) 0 (column + 1) ≈
      matrix (column + 1) 0 := by
  rw [finiteLDLGram_prepend_split]
  refine Q'.eqv_trans _
    (matrix 0 0 * (matrix (column + 1) 0 *
      Q'.recipPos (matrix 0 0) hpivot) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv _))
      (prepend_tail_zero_left n matrix
        (Q'.recipPos (matrix 0 0) hpivot) tailLower tailDiagonal (column + 1))
  · exact Q'.eqv_trans _
      (matrix 0 0 * (matrix (column + 1) 0 *
        Q'.recipPos (matrix 0 0) hpivot)) _
      (Q'.eqv_of_eq (Q'.add_zero' _))
      (pivot_mul_entry_mul_recipPos_eqv
        (matrix 0 0) (matrix (column + 1) 0) hpivot)

private theorem finiteLDLGram_prepend_succ_zero
    (n : Nat) (matrix : Nat → Nat → Q')
    (hpivot : (0 : Q') < matrix 0 0)
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (row : Nat) :
    finiteLDLGram (n + 1)
        (prependLower matrix (Q'.recipPos (matrix 0 0) hpivot) tailLower)
        (prependDiagonal matrix tailDiagonal) (row + 1) 0 ≈
      matrix (row + 1) 0 := by
  rw [finiteLDLGram_prepend_split]
  refine Q'.eqv_trans _
    (matrix 0 0 * ((matrix (row + 1) 0 *
      Q'.recipPos (matrix 0 0) hpivot) * 1) + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (prepend_tail_zero_right n matrix
        (Q'.recipPos (matrix 0 0) hpivot) tailLower tailDiagonal (row + 1))
  · exact Q'.eqv_trans _
      (matrix 0 0 * (matrix (row + 1) 0 *
        Q'.recipPos (matrix 0 0) hpivot) + 0) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.mul_one_eqv _)))
      (Q'.eqv_trans _
        (matrix 0 0 * (matrix (row + 1) 0 *
          Q'.recipPos (matrix 0 0) hpivot)) _
        (Q'.eqv_of_eq (Q'.add_zero' _))
        (pivot_mul_entry_mul_recipPos_eqv
          (matrix 0 0) (matrix (row + 1) 0) hpivot))

private theorem finiteLDLGram_prepend_succ_succ
    (n : Nat) (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (tailLower : Nat → Nat → Q') (tailDiagonal : Nat → Q')
    (row column : Nat) :
    finiteLDLGram (n + 1)
        (prependLower matrix pivotInverse tailLower)
        (prependDiagonal matrix tailDiagonal) (row + 1) (column + 1) =
      matrix 0 0 *
          ((matrix (row + 1) 0 * pivotInverse) *
            (matrix (column + 1) 0 * pivotInverse)) +
        finiteLDLGram n tailLower tailDiagonal row column := by
  rw [finiteLDLGram_prepend_split]
  rfl

private theorem prepend_headTerm_eqv_cross
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (hsymmetric : FiniteMatrixSymmetric (n + 1) matrix)
    {row column : Nat} (_hrow : row < n) (hcolumn : column < n) :
    matrix 0 0 *
        ((matrix (row + 1) 0 *
            Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)) *
          (matrix (column + 1) 0 *
            Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))) ≈
      matrix (row + 1) 0 *
        (matrix 0 (column + 1) *
          Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)) := by
  let reciprocal :=
    Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)
  have hcolumnHead :
      matrix (column + 1) 0 ≈ matrix 0 (column + 1) :=
    hsymmetric (by omega) (by omega)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv
        (matrix 0 0)
        (matrix (row + 1) 0 * reciprocal)
        (matrix (column + 1) 0 * reciprocal)))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (pivot_mul_entry_mul_recipPos_eqv
          (matrix 0 0) (matrix (row + 1) 0)
          (headPivot_positive hpositive)))
      (Q'.mul_eqv_congr_left (matrix (row + 1) 0) _ _
        (Q'.mul_eqv_congr_right _ _ _ hcolumnHead)))

/-- Prepend one positive pivot and exact Schur-tail factor. -/
def prependPositiveLDLData
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (hsymmetric : FiniteMatrixSymmetric (n + 1) matrix)
    (tail : PositiveLDLData n (finiteSchurPullback n matrix hpositive)) :
    PositiveLDLData (n + 1) matrix where
  lower := prependLower matrix
    (Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)) tail.lower
  diagonal := prependDiagonal matrix tail.diagonal
  entries := by
    intro row column hrow hcolumn
    cases row with
    | zero =>
        cases column with
        | zero =>
            exact Q'.eqv_symm
              (finiteLDLGram_prepend_zero_zero n matrix
                (Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))
                tail.lower tail.diagonal)
        | succ column =>
            have hcolumnTail : column < n := by omega
            exact Q'.eqv_trans _ (matrix (column + 1) 0) _
              (hsymmetric (by omega) (by omega))
              (Q'.eqv_symm
                (finiteLDLGram_prepend_zero_succ n matrix
                  (headPivot_positive hpositive) tail.lower tail.diagonal column))
    | succ row =>
        cases column with
        | zero =>
            exact Q'.eqv_symm
              (finiteLDLGram_prepend_succ_zero n matrix
                (headPivot_positive hpositive) tail.lower tail.diagonal row)
        | succ column =>
            have hrowTail : row < n := by omega
            have hcolumnTail : column < n := by omega
            rw [finiteLDLGram_prepend_succ_succ]
            apply Q'.eqv_symm
            refine Q'.eqv_trans _
              (matrix (row + 1) 0 *
                  (matrix 0 (column + 1) *
                    Q'.recipPos (matrix 0 0)
                      (headPivot_positive hpositive)) +
                finiteSchurPullback n matrix hpositive row column) _ ?_ ?_
            · exact Q'.add_eqv_congr'
                (prepend_headTerm_eqv_cross hpositive hsymmetric
                  hrowTail hcolumnTail)
                (Q'.eqv_symm
                  (tail.entries hrowTail hcolumnTail))
            · have hschur :=
                finiteSchurPullback_entry
                  hpositive hrowTail hcolumnTail
              have hcancel := add_cross_cancel_local
                (matrix (row + 1) 0 *
                  (matrix 0 (column + 1) *
                    Q'.recipPos (matrix 0 0)
                      (headPivot_positive hpositive)))
                (matrix (row + 1) (column + 1))
              exact Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr_left _ _ _ hschur)
                hcancel
  diagonal_pos := by
    intro index hindex
    cases index with
    | zero => exact headPivot_positive hpositive
    | succ index => exact tail.diagonal_pos (by omega)

/-- Recursive all-dimension exact positive LDL producer. -/
def positiveLDLDataOfStrictPositive :
    ∀ (n : Nat) (matrix : Nat → Nat → Q'),
      FiniteMatrixSymmetric n matrix →
      FiniteMatrixStrictlyPositive n matrix →
      PositiveLDLData n matrix
  | 0, matrix, _hsymmetric, _hpositive => PositiveLDLData.zero matrix
  | n + 1, matrix, hsymmetric, hpositive =>
      let tailPositive :
          FiniteMatrixStrictlyPositive n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_strictlyPositive hpositive
      let tailSymmetric :
          FiniteMatrixSymmetric n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_symmetric hpositive hsymmetric
      prependPositiveLDLData hpositive hsymmetric
        (positiveLDLDataOfStrictPositive n
          (finiteSchurPullback n matrix hpositive)
          tailSymmetric tailPositive)

/-- The unit-lower factor produced by the positive-LDL recursion has an
explicit constructive two-sided inverse. -/
def positiveLDLLowerInverseData :
    ∀ (n : Nat) (matrix : Nat → Nat → Q')
      (hsymmetric : FiniteMatrixSymmetric n matrix)
      (hpositive : FiniteMatrixStrictlyPositive n matrix),
      UnitLowerInverseData n
        (positiveLDLDataOfStrictPositive
          n matrix hsymmetric hpositive).lower
  | 0, matrix, hsymmetric, hpositive => by
      exact UnitLowerInverseData.zero
        (positiveLDLDataOfStrictPositive
          0 matrix hsymmetric hpositive).lower
  | n + 1, matrix, hsymmetric, hpositive => by
      let tailPositive :
          FiniteMatrixStrictlyPositive n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_strictlyPositive hpositive
      let tailSymmetric :
          FiniteMatrixSymmetric n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_symmetric hpositive hsymmetric
      let tailInverse := positiveLDLLowerInverseData n
        (finiteSchurPullback n matrix hpositive)
        tailSymmetric tailPositive
      change UnitLowerInverseData (n + 1)
        (prependLower matrix
          (Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))
          (positiveLDLDataOfStrictPositive n
            (finiteSchurPullback n matrix hpositive)
            tailSymmetric tailPositive).lower)
      exact prependUnitLowerInverseData
        (fun row => matrix (row + 1) 0 *
          Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))
        tailInverse

/-- The recursively produced positive-LDL lower factor is unit-lower. -/
theorem positiveLDLDataOfStrictPositive_isUnitLower :
    ∀ (n : Nat) (matrix : Nat → Nat → Q')
      (hsymmetric : FiniteMatrixSymmetric n matrix)
      (hpositive : FiniteMatrixStrictlyPositive n matrix),
      IsUnitLower n
        (positiveLDLDataOfStrictPositive
          n matrix hsymmetric hpositive).lower
  | 0, matrix, hsymmetric, hpositive => by
      exact isUnitLower_zero
        (positiveLDLDataOfStrictPositive
          0 matrix hsymmetric hpositive).lower
  | n + 1, matrix, hsymmetric, hpositive => by
      let tailPositive :
          FiniteMatrixStrictlyPositive n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_strictlyPositive hpositive
      let tailSymmetric :
          FiniteMatrixSymmetric n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_symmetric hpositive hsymmetric
      change IsUnitLower (n + 1)
        (prependLower matrix
          (Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))
          (positiveLDLDataOfStrictPositive n
            (finiteSchurPullback n matrix hpositive)
            tailSymmetric tailPositive).lower)
      unfold prependLower
      exact prependUnitLower_isUnitLower _ _
        (positiveLDLDataOfStrictPositive_isUnitLower n
          (finiteSchurPullback n matrix hpositive)
          tailSymmetric tailPositive)

/-- The explicit inverse of the recursively produced lower factor is also
unit-lower. -/
theorem positiveLDLLowerInverseData_isUnitLower :
    ∀ (n : Nat) (matrix : Nat → Nat → Q')
      (hsymmetric : FiniteMatrixSymmetric n matrix)
      (hpositive : FiniteMatrixStrictlyPositive n matrix),
      IsUnitLower n
        (positiveLDLLowerInverseData
          n matrix hsymmetric hpositive).inverse
  | 0, matrix, hsymmetric, hpositive => by
      exact isUnitLower_zero
        (positiveLDLLowerInverseData
          0 matrix hsymmetric hpositive).inverse
  | n + 1, matrix, hsymmetric, hpositive => by
      let tailPositive :
          FiniteMatrixStrictlyPositive n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_strictlyPositive hpositive
      let tailSymmetric :
          FiniteMatrixSymmetric n
            (finiteSchurPullback n matrix hpositive) :=
        finiteSchurPullback_symmetric hpositive hsymmetric
      change IsUnitLower (n + 1)
        (prependUnitLowerInverse n
          (fun row => matrix (row + 1) 0 *
            Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))
          (positiveLDLLowerInverseData n
            (finiteSchurPullback n matrix hpositive)
            tailSymmetric tailPositive).inverse)
      exact prependUnitLowerInverse_isUnitLower _ _
        (positiveLDLLowerInverseData_isUnitLower n
          (finiteSchurPullback n matrix hpositive)
          tailSymmetric tailPositive)

private theorem listQSum_member_le_nonnegative
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      value witness ≤ listQSum value items
  | [], _, _, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.add_le_self_of_nonneg
          (value head) (listQSum value tail)
          (listQSum_nonnegative_on value tail
            (fun item hitem =>
              hnonnegative item (List.mem_cons_of_mem head hitem)))
      · have htailLe := listQSum_member_le_nonnegative
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail
        have hsumLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.le_trans' _ _ _ htailLe hsumLe

/-- Every produced positive pivot is bounded above by the corresponding
diagonal entry of the original matrix. -/
theorem positiveLDLDataOfStrictPositive_diagonal_le_matrix_diagonal
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix)
    {index : Nat} (hindex : index < n) :
    (positiveLDLDataOfStrictPositive
        n matrix hsymmetric hpositive).diagonal index ≤
      matrix index index := by
  let data := positiveLDLDataOfStrictPositive
    n matrix hsymmetric hpositive
  let value := fun channel =>
    data.diagonal channel *
      (data.lower index channel * data.lower index channel)
  have hshape := positiveLDLDataOfStrictPositive_isUnitLower
    n matrix hsymmetric hpositive
  have hselected : value index ≈ data.diagonal index := by
    unfold value
    rw [hshape.1 hindex]
    exact Q'.eqv_trans _ (data.diagonal index * 1) _
      (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1))
      (Q'.mul_one_eqv _)
  have hterm : value index ≤ listQSum value (List.range n) :=
    listQSum_member_le_nonnegative value (List.range n)
      (fun channel hchannel =>
        Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (data.diagonal_pos (List.mem_range.mp hchannel)))
          (SumOfSquares.q_mul_self_nonneg (data.lower index channel)))
      (List.mem_range.mpr hindex)
  have hdiagonal : data.diagonal index ≤ finiteLDLGram n
      data.lower data.diagonal index index := by
    unfold finiteLDLGram
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_symm hselected)) hterm
  exact Q'.le_trans' _ _ _ hdiagonal
    (Q'.le_of_eqv (Q'.eqv_symm (data.entries hindex hindex)))

/-- The recursively produced factors pass the existing finite Boolean LDL
checker. -/
theorem positiveLDLDataOfStrictPositive_check
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    finiteLDLCheck n matrix
        (positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive).lower
        (positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive).diagonal =
      true :=
  PositiveLDLData.finiteLDLCheck_eq_true
    (positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive)

end YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer

#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.prependPositiveLDLData
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLDataOfStrictPositive
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLLowerInverseData
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLDataOfStrictPositive_isUnitLower
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLLowerInverseData_isUnitLower
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLDataOfStrictPositive_diagonal_le_matrix_diagonal
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer.positiveLDLDataOfStrictPositive_check
