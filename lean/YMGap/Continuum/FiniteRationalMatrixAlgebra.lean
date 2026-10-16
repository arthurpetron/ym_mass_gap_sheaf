/-
# Constructive finite rational matrix algebra

This module supplies the exact setoid algebra missing between the repository's
literal finite matrix product and the constructive positive-LDL producer.  It
proves product congruence, associativity, identity laws, transpose reversal,
and diagonal multiplication on in-range entries.

The immediate consumer is the explicit inverse built from the positive LDL
factors.  No determinant, dimension theorem, classical choice, Gaussian law,
continuum limit, or mass-gap statement is used or proved here.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
import YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

namespace YMGap.Continuum.FiniteRationalMatrixAlgebra

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

/-- Entrywise equivalence on the in-range square block. -/
def FiniteMatrixEqv
    (n : Nat) (left right : Nat → Nat → Q') : Prop :=
  ∀ {row column : Nat}, row < n → column < n →
    left row column ≈ right row column

theorem finiteMatrixEqv_refl
    (n : Nat) (matrix : Nat → Nat → Q') :
    FiniteMatrixEqv n matrix matrix := by
  intro row column _hrow _hcolumn
  exact Q'.eqv_refl _

theorem finiteMatrixEqv_symm
    {n : Nat} {left right : Nat → Nat → Q'}
    (heq : FiniteMatrixEqv n left right) :
    FiniteMatrixEqv n right left := by
  intro row column hrow hcolumn
  exact Q'.eqv_symm (heq hrow hcolumn)

theorem finiteMatrixEqv_trans
    {n : Nat} {first second third : Nat → Nat → Q'}
    (hfirst : FiniteMatrixEqv n first second)
    (hsecond : FiniteMatrixEqv n second third) :
    FiniteMatrixEqv n first third := by
  intro row column hrow hcolumn
  exact Q'.eqv_trans _ _ _
    (hfirst hrow hcolumn) (hsecond hrow hcolumn)

/-- Literal matrix transpose. -/
def finiteMatrixTranspose
    (matrix : Nat → Nat → Q') (row column : Nat) : Q' :=
  matrix column row

/-- Literal diagonal matrix. -/
def finiteDiagonalMatrix
    (diagonal : Nat → Q') (row column : Nat) : Q' :=
  if row = column then diagonal row else 0

theorem finiteMatrixProduct_congr
    {n : Nat}
    {leftA leftB rightA rightB : Nat → Nat → Q'}
    (hleft : FiniteMatrixEqv n leftA leftB)
    (hright : FiniteMatrixEqv n rightA rightB) :
    FiniteMatrixEqv n
      (finiteMatrixProduct n leftA rightA)
      (finiteMatrixProduct n leftB rightB) := by
  intro row column hrow hcolumn
  unfold finiteMatrixProduct
  apply listQSum_congr_on
  intro index hindex
  exact Q'.eqv_trans _
    (leftB row index * rightA index column) _
    (Q'.mul_eqv_congr_right _ _ _
      (hleft hrow (List.mem_range.mp hindex)))
    (Q'.mul_eqv_congr_left _ _ _
      (hright (List.mem_range.mp hindex) hcolumn))

/-- Associativity of the literal finite matrix product on in-range entries. -/
theorem finiteMatrixProduct_assoc
    (n : Nat) (first second third : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n (finiteMatrixProduct n first second) third)
      (finiteMatrixProduct n first (finiteMatrixProduct n second third)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct
  let indices := List.range n
  refine Q'.eqv_trans _
    (listQSum
      (fun middleRight => listQSum
        (fun middleLeft =>
          (first row middleLeft * second middleLeft middleRight) *
            third middleRight column)
        indices)
      indices) _ ?_ ?_
  · apply listQSum_congr
    intro middleRight
    exact Q'.eqv_symm
      (listQSum_mul_right
        (fun middleLeft =>
          first row middleLeft * second middleLeft middleRight)
        (third middleRight column) indices)
  · refine Q'.eqv_trans _
      (listQSum
        (fun middleLeft => listQSum
          (fun middleRight =>
            (first row middleLeft * second middleLeft middleRight) *
              third middleRight column)
          indices)
        indices) _
      (listQSum_swap
        (fun middleLeft middleRight =>
          (first row middleLeft * second middleLeft middleRight) *
            third middleRight column)
        indices indices) ?_
    apply listQSum_congr
    intro middleLeft
    refine Q'.eqv_trans _
      (listQSum
        (fun middleRight =>
          first row middleLeft *
            (second middleLeft middleRight * third middleRight column))
        indices) _ ?_ ?_
    · exact listQSum_congr
        (fun middleRight => Q'.mul_assoc_eqv
          (first row middleLeft) (second middleLeft middleRight)
          (third middleRight column)) indices
    · exact listQSum_mul_left
        (first row middleLeft)
        (fun middleRight =>
          second middleLeft middleRight * third middleRight column)
        indices

theorem finiteIdentityMatrix_mul
    (n : Nat) (matrix : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n finiteIdentityMatrix matrix) matrix := by
  intro row column hrow _hcolumn
  unfold finiteMatrixProduct finiteIdentityMatrix
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if row = index then matrix index column else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases heq : row = index
    · rw [if_pos heq, if_pos heq]
      exact Q'.one_mul_eqv _
    · rw [if_neg heq, if_neg heq]
      exact Q'.zero_mul_eqv _
  · exact listQSum_ite_single row
      (fun index => matrix index column) (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hrow)

theorem finiteMatrix_mul_identity
    (n : Nat) (matrix : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n matrix finiteIdentityMatrix) matrix := by
  intro row column _hrow hcolumn
  unfold finiteMatrixProduct finiteIdentityMatrix
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if column = index then matrix row index else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases heq : column = index
    · have hreverse : index = column := heq.symm
      rw [if_pos heq, if_pos hreverse]
      exact Q'.mul_one_eqv _
    · have hreverse : index ≠ column := fun h => heq h.symm
      rw [if_neg heq, if_neg hreverse]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single column
      (fun index => matrix row index) (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hcolumn)

theorem finiteMatrixTranspose_product
    (n : Nat) (left right : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixTranspose (finiteMatrixProduct n left right))
      (finiteMatrixProduct n
        (finiteMatrixTranspose right) (finiteMatrixTranspose left)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixTranspose finiteMatrixProduct
  exact listQSum_congr
    (fun index => Q'.mul_comm_eqv
      (left column index) (right index row))
    (List.range n)

theorem finiteMatrixTranspose_congr
    {n : Nat} {left right : Nat → Nat → Q'}
    (heq : FiniteMatrixEqv n left right) :
    FiniteMatrixEqv n
      (finiteMatrixTranspose left) (finiteMatrixTranspose right) := by
  intro row column hrow hcolumn
  exact heq hcolumn hrow

theorem finiteIdentityMatrix_transpose (row column : Nat) :
    finiteMatrixTranspose finiteIdentityMatrix row column =
      finiteIdentityMatrix row column := by
  unfold finiteMatrixTranspose finiteIdentityMatrix
  by_cases heq : row = column
  · subst column
    rw [if_pos rfl]
  · have hreverse : column ≠ row := fun h => heq h.symm
    rw [if_neg heq, if_neg hreverse]

theorem finiteIdentityMatrix_transpose_eqv (n : Nat) :
    FiniteMatrixEqv n
      (finiteMatrixTranspose finiteIdentityMatrix) finiteIdentityMatrix := by
  intro row column _hrow _hcolumn
  exact Q'.eqv_of_eq (finiteIdentityMatrix_transpose row column)

/-- Right multiplication by a literal diagonal matrix scales the selected
column. -/
theorem finiteMatrixProduct_right_diagonal
    (n : Nat) (matrix : Nat → Nat → Q') (diagonal : Nat → Q')
    (row : Nat) {column : Nat} (hcolumn : column < n) :
    finiteMatrixProduct n matrix (finiteDiagonalMatrix diagonal)
        row column ≈
      matrix row column * diagonal column := by
  unfold finiteMatrixProduct finiteDiagonalMatrix
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        if column = index then matrix row index * diagonal index else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases heq : column = index
    · subst index
      rw [if_pos rfl, if_pos rfl]
      exact Q'.eqv_refl _
    · have hreverse : index ≠ column := fun h => heq h.symm
      rw [if_neg heq, if_neg hreverse]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single column
      (fun index => matrix row index * diagonal index)
      (List.range n) (rangeNodupLocal n)
      (List.mem_range.mpr hcolumn)

/-- The repository's weighted-Gram LDL entry is exactly the ordinary product
`(L D) Lᵀ`. -/
theorem finiteLDLGram_eq_product
    (n : Nat) (lower : Nat → Nat → Q') (diagonal : Nat → Q')
    (row column : Nat) :
    finiteLDLGram n lower diagonal row column ≈
      finiteMatrixProduct n
        (finiteMatrixProduct n lower (finiteDiagonalMatrix diagonal))
        (finiteMatrixTranspose lower) row column := by
  unfold finiteLDLGram finiteMatrixProduct finiteMatrixTranspose
  apply listQSum_congr_on
  intro index hindex
  have hscale := finiteMatrixProduct_right_diagonal
    n lower diagonal row (List.mem_range.mp hindex)
  exact Q'.eqv_trans _
    ((lower row index * diagonal index) * lower column index) _
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (diagonal index)
          (lower row index) (lower column index)))
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_comm_eqv (diagonal index) (lower row index))))
    (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hscale))

theorem finiteMatrixEqv_of_ldl_entries
    {n : Nat} {matrix lower : Nat → Nat → Q'}
    {diagonal : Nat → Q'}
    (hentries : ∀ {row column : Nat}, row < n → column < n →
      matrix row column ≈ finiteLDLGram n lower diagonal row column) :
    FiniteMatrixEqv n matrix
      (finiteMatrixProduct n
        (finiteMatrixProduct n lower (finiteDiagonalMatrix diagonal))
        (finiteMatrixTranspose lower)) := by
  intro row column hrow hcolumn
  exact Q'.eqv_trans _ _ _
    (hentries hrow hcolumn)
    (finiteLDLGram_eq_product n lower diagonal row column)

/-- Multiplication of two literal diagonal matrices collapses entrywise. -/
theorem finiteDiagonalMatrix_product
    (n : Nat) (left right : Nat → Q')
    {row column : Nat} (hrow : row < n) :
    finiteMatrixProduct n
        (finiteDiagonalMatrix left) (finiteDiagonalMatrix right)
        row column ≈
      if row = column then left row * right row else 0 := by
  unfold finiteMatrixProduct finiteDiagonalMatrix
  refine Q'.eqv_trans _
    (listQSum
      (fun index =>
        if row = index then
          left row * (if row = column then right row else 0)
        else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    by_cases hrowIndex : row = index
    · subst index
      rw [if_pos rfl, if_pos rfl]
      exact Q'.eqv_refl _
    · rw [if_neg hrowIndex, if_neg hrowIndex]
      exact Q'.zero_mul_eqv _
  · refine Q'.eqv_trans _
      (left row * (if row = column then right row else 0)) _
      (listQSum_ite_single row
        (fun _index =>
          left row * (if row = column then right row else 0))
        (List.range n) (rangeNodupLocal n)
        (List.mem_range.mpr hrow)) ?_
    by_cases hrowColumn : row = column
    · simp only [if_pos hrowColumn]
      exact Q'.eqv_refl _
    · simp only [if_neg hrowColumn]
      exact Q'.mul_zero_eqv _

end YMGap.Continuum.FiniteRationalMatrixAlgebra

#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteMatrixProduct_assoc
#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteIdentityMatrix_mul
#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteMatrix_mul_identity
#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteMatrixTranspose_product
#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteLDLGram_eq_product
#print axioms YMGap.Continuum.FiniteRationalMatrixAlgebra.finiteDiagonalMatrix_product
