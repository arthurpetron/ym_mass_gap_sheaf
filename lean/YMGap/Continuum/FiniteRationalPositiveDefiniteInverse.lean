/-
# Constructive inverse of finite strictly positive rational matrices

This module composes the all-dimension positive LDL producer with the explicit
unit-lower inverse.  Positive pivots provide literal rational reciprocals, and
the inverse is the exact factor product

    L⁻ᵀ D⁻¹ L⁻¹.

Both multiplication orders are proved in the repository's rational setoid and
compiled to the existing executable inverse checker.  No determinant,
classical choice, external certificate oracle, Gaussian law, continuum limit,
or mass-gap statement is used or proved here.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer

namespace YMGap.Continuum.FiniteRationalPositiveDefiniteInverse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDLProducer
open YMGap.Continuum.FiniteRationalUnitLowerInverse
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_positive_of_mem
    {A : Type} (value : A → Q') :
    ∀ (items : List A) {witness : A},
      (∀ item, item ∈ items → (0 : Q') ≤ value item) →
      witness ∈ items →
      (0 : Q') < value witness →
      (0 : Q') < listQSum value items
  | [], _, _, hmem, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, witness, hnonnegative, hmem, hwitness => by
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst witness
        exact Q'.pos_of_lt_of_le hwitness
          (Q'.add_le_self_of_nonneg
            (value head) (listQSum value tail)
            (listQSum_nonnegative_on value tail
              (fun item hitem =>
                hnonnegative item
                  (List.mem_cons_of_mem head hitem))))
      · have htailPositive := listQSum_positive_of_mem
          value tail
          (fun item hitem =>
            hnonnegative item (List.mem_cons_of_mem head hitem))
          htail hwitness
        have htailLe :
            listQSum value tail ≤ value head + listQSum value tail := by
          have h := Q'.add_le_add_right
            (0 : Q') (value head) (listQSum value tail)
            (hnonnegative head List.mem_cons_self)
          rwa [Q'.zero_add'] at h
        exact Q'.pos_of_lt_of_le htailPositive htailLe

private def listQSumNonzeroWitness
    {A : Type} (value : A → Q') :
    ∀ items : List A, ¬ listQSum value items ≈ 0 →
      Σ' witness : A, witness ∈ items ∧ ¬ value witness ≈ 0
  | [], hnonzero => False.elim (hnonzero (Q'.eqv_refl 0))
  | head :: tail, hnonzero => by
      by_cases hhead : value head ≈ 0
      · have htail : ¬ listQSum value tail ≈ 0 := by
          intro htail
          exact hnonzero
            (Q'.eqv_trans _ (0 + 0) _
              (Q'.add_eqv_congr' hhead htail)
              (Q'.eqv_of_eq (Q'.zero_add' 0)))
        let witness := listQSumNonzeroWitness value tail htail
        exact ⟨witness.1,
          List.mem_cons_of_mem head witness.2.1, witness.2.2⟩
      · exact ⟨head, List.mem_cons_self, hhead⟩

private theorem eqvZero_of_numZero_local {value : Q'}
    (hnum : value.num = 0) : value ≈ 0 := by
  show value.num * ((0 : Q').den : Int) =
    (0 : Q').num * (value.den : Int)
  rw [hnum, show (0 : Q').num = 0 from rfl,
    Int.zero_mul, Int.zero_mul]

private theorem positive_of_nonnegative_not_eqv_zero_local
    {value : Q'} (hnonnegative : (0 : Q') ≤ value)
    (hne : ¬ value ≈ 0) : (0 : Q') < value := by
  have hnumNonnegative : (0 : Int) ≤ value.num :=
    (Q'.zero_le_iff_num_nonneg value).mp hnonnegative
  have hnumNe : value.num ≠ 0 := by
    intro hnum
    exact hne (eqvZero_of_numZero_local hnum)
  show (0 : Int) * (value.den : Int) < value.num * (1 : Int)
  rw [Int.zero_mul, Int.mul_one]
  omega

private theorem square_not_eqv_zero_local {value : Q'}
    (hne : ¬ value ≈ 0) : ¬ value * value ≈ 0 := by
  intro hsquare
  have hnumSquare : value.num * value.num = 0 := by
    have hcross := hsquare
    have hzeroDen : ((0 : Q').den : Int) = 1 := rfl
    have hzeroNum : (0 : Q').num = 0 := rfl
    have hmulNum : (value * value).num = value.num * value.num := rfl
    change
      (value.num * value.num) * ((0 : Q').den : Int) =
        (0 : Q').num * ((value * value).den : Int) at hcross
    rw [hzeroDen, hzeroNum, Int.mul_one, Int.zero_mul] at hcross
    exact hcross
  exact hne (eqvZero_of_numZero_local
    ((Int.mul_eq_zero.mp hnumSquare).elim id id))

private def repeatedColumn
    (vector : Nat → Q') (row _column : Nat) : Q' :=
  vector row

private theorem finiteMatrixVectorApply_product
    (n : Nat) (left right : Nat → Nat → Q')
    (vector : Nat → Q') {row : Nat} (hrow : row < n) :
    finiteMatrixVectorApply n left
        (finiteMatrixVectorApply n right vector) row ≈
      finiteMatrixVectorApply n (finiteMatrixProduct n left right)
        vector row := by
  have hzero : 0 < n := Nat.zero_lt_of_lt hrow
  have hassoc := finiteMatrixProduct_assoc n left right
    (repeatedColumn vector) hrow hzero
  exact Q'.eqv_symm hassoc

private theorem finiteMatrixVectorApply_congr
    {n : Nat} {left right : Nat → Nat → Q'}
    (heq : FiniteMatrixEqv n left right)
    (vector : Nat → Q') {row : Nat} (hrow : row < n) :
    finiteMatrixVectorApply n left vector row ≈
      finiteMatrixVectorApply n right vector row := by
  unfold finiteMatrixVectorApply
  apply listQSum_congr_on
  intro column hcolumn
  exact Q'.mul_eqv_congr_right _ _ _
    (heq hrow (List.mem_range.mp hcolumn))

private theorem finiteIdentityMatrix_vectorApply
    (n : Nat) (vector : Nat → Q') {row : Nat} (hrow : row < n) :
    finiteMatrixVectorApply n finiteIdentityMatrix vector row ≈
      vector row := by
  have hzero : 0 < n := Nat.zero_lt_of_lt hrow
  exact finiteIdentityMatrix_mul n (repeatedColumn vector) hrow hzero

private theorem channelLinear_transpose_eq_vectorApply
    (n : Nat) (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') (channel : Nat) :
    channelLinear (List.range n) (finiteMatrixTranspose matrix)
        coefficient channel ≈
      finiteMatrixVectorApply n matrix coefficient channel := by
  unfold channelLinear finiteMatrixTranspose finiteMatrixVectorApply
  exact listQSum_congr
    (fun index => Q'.mul_comm_eqv
      (coefficient index) (matrix channel index))
    (List.range n)

/-- Type-level exact two-sided inverse data. -/
structure FiniteMatrixInverseData
    (n : Nat) (matrix : Nat → Nat → Q') : Type where
  inverse : Nat → Nat → Q'
  matrix_inverse : FiniteMatrixEqv n
    (finiteMatrixProduct n matrix inverse) finiteIdentityMatrix
  inverse_matrix : FiniteMatrixEqv n
    (finiteMatrixProduct n inverse matrix) finiteIdentityMatrix

namespace FiniteMatrixInverseData

/-- Exact inverse data passes the existing finite Boolean two-sided checker. -/
theorem finiteMatrixInverseCheck_eq_true
    {n : Nat} {matrix : Nat → Nat → Q'}
    (data : FiniteMatrixInverseData n matrix) :
    finiteMatrixInverseCheck n matrix data.inverse = true := by
  unfold finiteMatrixInverseCheck
  apply List.all_eq_true.mpr
  intro row hrow
  apply List.all_eq_true.mpr
  intro column hcolumn
  apply (Bool.and_eq_true _ _).mpr
  exact ⟨decide_eq_true
      (data.matrix_inverse
        (List.mem_range.mp hrow) (List.mem_range.mp hcolumn)),
    decide_eq_true
      (data.inverse_matrix
        (List.mem_range.mp hrow) (List.mem_range.mp hcolumn))⟩

end FiniteMatrixInverseData

/-- Total diagonal reciprocal, using zero only outside the finite positive
block. -/
def positiveDiagonalReciprocal
    (n : Nat) (diagonal : Nat → Q')
    (hpositive : ∀ {index : Nat}, index < n → (0 : Q') < diagonal index)
    (index : Nat) : Q' :=
  if hindex : index < n then
    Q'.recipPos (diagonal index) (hpositive hindex)
  else 0

theorem finitePositiveDiagonal_mul_reciprocal
    (n : Nat) (diagonal : Nat → Q')
    (hpositive : ∀ {index : Nat}, index < n → (0 : Q') < diagonal index) :
    FiniteMatrixEqv n
      (finiteMatrixProduct n
        (finiteDiagonalMatrix diagonal)
        (finiteDiagonalMatrix
          (positiveDiagonalReciprocal n diagonal hpositive)))
      finiteIdentityMatrix := by
  intro row column hrow _hcolumn
  refine Q'.eqv_trans _
    (if row = column then
      diagonal row * positiveDiagonalReciprocal n diagonal hpositive row
    else 0) _
    (finiteDiagonalMatrix_product n diagonal
      (positiveDiagonalReciprocal n diagonal hpositive) hrow) ?_
  unfold finiteIdentityMatrix
  by_cases heq : row = column
  · subst column
    rw [if_pos rfl, if_pos rfl]
    unfold positiveDiagonalReciprocal
    rw [dif_pos hrow]
    exact Q'.mul_recipPos_eqv _ _
  · rw [if_neg heq, if_neg heq]
    exact Q'.eqv_refl _

theorem finitePositiveReciprocal_mul_diagonal
    (n : Nat) (diagonal : Nat → Q')
    (hpositive : ∀ {index : Nat}, index < n → (0 : Q') < diagonal index) :
    FiniteMatrixEqv n
      (finiteMatrixProduct n
        (finiteDiagonalMatrix
          (positiveDiagonalReciprocal n diagonal hpositive))
        (finiteDiagonalMatrix diagonal))
      finiteIdentityMatrix := by
  intro row column hrow _hcolumn
  refine Q'.eqv_trans _
    (if row = column then
      positiveDiagonalReciprocal n diagonal hpositive row * diagonal row
    else 0) _
    (finiteDiagonalMatrix_product n
      (positiveDiagonalReciprocal n diagonal hpositive) diagonal hrow) ?_
  unfold finiteIdentityMatrix
  by_cases heq : row = column
  · subst column
    rw [if_pos rfl, if_pos rfl]
    unfold positiveDiagonalReciprocal
    rw [dif_pos hrow]
    exact Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv _ _)
  · rw [if_neg heq, if_neg heq]
    exact Q'.eqv_refl _

/-- Exact inverse factor assembled from positive LDL data and a two-sided
inverse of its unit-lower factor. -/
def positiveLDLInverseMatrix
    {n : Nat} {matrix : Nat → Nat → Q'}
    (data : PositiveLDLData n matrix)
    (lowerInverse : UnitLowerInverseData n data.lower) :
    Nat → Nat → Q' :=
  finiteMatrixProduct n
    (finiteMatrixTranspose lowerInverse.inverse)
    (finiteMatrixProduct n
      (finiteDiagonalMatrix
        (positiveDiagonalReciprocal n data.diagonal data.diagonal_pos))
      lowerInverse.inverse)

/-- Positive LDL data with its constructive unit-lower inverse yields exact
two-sided inverse data for the original matrix. -/
def finiteMatrixInverseDataOfPositiveLDL
    {n : Nat} {matrix : Nat → Nat → Q'}
    (data : PositiveLDLData n matrix)
    (lowerInverse : UnitLowerInverseData n data.lower) :
    FiniteMatrixInverseData n matrix where
  inverse := positiveLDLInverseMatrix data lowerInverse
  matrix_inverse := by
    let lower := data.lower
    let diagonal := finiteDiagonalMatrix data.diagonal
    let lowerInv := lowerInverse.inverse
    let diagonalInv := finiteDiagonalMatrix
      (positiveDiagonalReciprocal n data.diagonal data.diagonal_pos)
    let lowerT := finiteMatrixTranspose lower
    let lowerInvT := finiteMatrixTranspose lowerInv
    let inverse := finiteMatrixProduct n lowerInvT
      (finiteMatrixProduct n diagonalInv lowerInv)
    change FiniteMatrixEqv n
      (finiteMatrixProduct n matrix inverse) finiteIdentityMatrix
    have hmatrix : FiniteMatrixEqv n matrix
        (finiteMatrixProduct n
          (finiteMatrixProduct n lower diagonal) lowerT) := by
      exact finiteMatrixEqv_of_ldl_entries data.entries
    have hdiagonal : FiniteMatrixEqv n
        (finiteMatrixProduct n diagonal diagonalInv)
        finiteIdentityMatrix := by
      exact finitePositiveDiagonal_mul_reciprocal
        n data.diagonal data.diagonal_pos
    have hlowerTInvT : FiniteMatrixEqv n
        (finiteMatrixProduct n lowerT lowerInvT)
        finiteIdentityMatrix := by
      exact finiteMatrixEqv_trans
        (finiteMatrixEqv_symm
          (finiteMatrixTranspose_product n lowerInv lower))
        (finiteMatrixEqv_trans
          (finiteMatrixTranspose_congr lowerInverse.inverse_lower)
          (finiteIdentityMatrix_transpose_eqv n))
    have htail : FiniteMatrixEqv n
        (finiteMatrixProduct n lowerT
          (finiteMatrixProduct n lowerInvT
            (finiteMatrixProduct n diagonalInv lowerInv)))
        (finiteMatrixProduct n diagonalInv lowerInv) := by
      exact finiteMatrixEqv_trans
        (finiteMatrixEqv_symm
          (finiteMatrixProduct_assoc n lowerT lowerInvT
            (finiteMatrixProduct n diagonalInv lowerInv)))
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr hlowerTInvT
            (finiteMatrixEqv_refl n
              (finiteMatrixProduct n diagonalInv lowerInv)))
          (finiteIdentityMatrix_mul n
            (finiteMatrixProduct n diagonalInv lowerInv)))
    have hdiagonalTail : FiniteMatrixEqv n
        (finiteMatrixProduct n diagonal
          (finiteMatrixProduct n diagonalInv lowerInv)) lowerInv := by
      exact finiteMatrixEqv_trans
        (finiteMatrixEqv_symm
          (finiteMatrixProduct_assoc n diagonal diagonalInv lowerInv))
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr hdiagonal
            (finiteMatrixEqv_refl n lowerInv))
          (finiteIdentityMatrix_mul n lowerInv))
    have hfactor : FiniteMatrixEqv n
        (finiteMatrixProduct n
          (finiteMatrixProduct n
            (finiteMatrixProduct n lower diagonal) lowerT)
          inverse)
        finiteIdentityMatrix := by
      exact finiteMatrixEqv_trans
        (finiteMatrixProduct_assoc n
          (finiteMatrixProduct n lower diagonal) lowerT inverse)
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr
            (finiteMatrixEqv_refl n
              (finiteMatrixProduct n lower diagonal)) htail)
          (finiteMatrixEqv_trans
            (finiteMatrixProduct_assoc n lower diagonal
              (finiteMatrixProduct n diagonalInv lowerInv))
            (finiteMatrixEqv_trans
              (finiteMatrixProduct_congr
                (finiteMatrixEqv_refl n lower) hdiagonalTail)
              lowerInverse.lower_inverse)))
    intro row column hrow hcolumn
    exact Q'.eqv_trans _ _ _
      ((finiteMatrixProduct_congr hmatrix
        (finiteMatrixEqv_refl n inverse)) hrow hcolumn)
      (hfactor hrow hcolumn)
  inverse_matrix := by
    let lower := data.lower
    let diagonal := finiteDiagonalMatrix data.diagonal
    let lowerInv := lowerInverse.inverse
    let diagonalInv := finiteDiagonalMatrix
      (positiveDiagonalReciprocal n data.diagonal data.diagonal_pos)
    let lowerT := finiteMatrixTranspose lower
    let lowerInvT := finiteMatrixTranspose lowerInv
    let inverse := finiteMatrixProduct n lowerInvT
      (finiteMatrixProduct n diagonalInv lowerInv)
    change FiniteMatrixEqv n
      (finiteMatrixProduct n inverse matrix) finiteIdentityMatrix
    have hmatrix : FiniteMatrixEqv n matrix
        (finiteMatrixProduct n
          (finiteMatrixProduct n lower diagonal) lowerT) := by
      exact finiteMatrixEqv_of_ldl_entries data.entries
    have hdiagonal : FiniteMatrixEqv n
        (finiteMatrixProduct n diagonalInv diagonal)
        finiteIdentityMatrix := by
      exact finitePositiveReciprocal_mul_diagonal
        n data.diagonal data.diagonal_pos
    have hlowerInvLower : FiniteMatrixEqv n
        (finiteMatrixProduct n lowerInv lower) finiteIdentityMatrix :=
      lowerInverse.inverse_lower
    have hlowerInvLowerDiagonal : FiniteMatrixEqv n
        (finiteMatrixProduct n lowerInv
          (finiteMatrixProduct n lower diagonal)) diagonal := by
      exact finiteMatrixEqv_trans
        (finiteMatrixEqv_symm
          (finiteMatrixProduct_assoc n lowerInv lower diagonal))
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr hlowerInvLower
            (finiteMatrixEqv_refl n diagonal))
          (finiteIdentityMatrix_mul n diagonal))
    have hmiddle : FiniteMatrixEqv n
        (finiteMatrixProduct n
          (finiteMatrixProduct n diagonalInv lowerInv)
          (finiteMatrixProduct n
            (finiteMatrixProduct n lower diagonal) lowerT))
        lowerT := by
      exact finiteMatrixEqv_trans
        (finiteMatrixProduct_assoc n diagonalInv lowerInv
          (finiteMatrixProduct n
            (finiteMatrixProduct n lower diagonal) lowerT))
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr
            (finiteMatrixEqv_refl n diagonalInv)
            (finiteMatrixEqv_trans
              (finiteMatrixEqv_symm
                (finiteMatrixProduct_assoc n lowerInv
                  (finiteMatrixProduct n lower diagonal) lowerT))
              (finiteMatrixProduct_congr hlowerInvLowerDiagonal
                (finiteMatrixEqv_refl n lowerT))))
          (finiteMatrixEqv_trans
            (finiteMatrixEqv_symm
              (finiteMatrixProduct_assoc n diagonalInv diagonal lowerT))
            (finiteMatrixEqv_trans
              (finiteMatrixProduct_congr hdiagonal
                (finiteMatrixEqv_refl n lowerT))
              (finiteIdentityMatrix_mul n lowerT))))
    have hlowerInvTLowerT : FiniteMatrixEqv n
        (finiteMatrixProduct n lowerInvT lowerT)
        finiteIdentityMatrix := by
      exact finiteMatrixEqv_trans
        (finiteMatrixEqv_symm
          (finiteMatrixTranspose_product n lower lowerInv))
        (finiteMatrixEqv_trans
          (finiteMatrixTranspose_congr lowerInverse.lower_inverse)
          (finiteIdentityMatrix_transpose_eqv n))
    have hfactor : FiniteMatrixEqv n
        (finiteMatrixProduct n inverse
          (finiteMatrixProduct n
            (finiteMatrixProduct n lower diagonal) lowerT))
        finiteIdentityMatrix := by
      exact finiteMatrixEqv_trans
        (finiteMatrixProduct_assoc n lowerInvT
          (finiteMatrixProduct n diagonalInv lowerInv)
          (finiteMatrixProduct n
            (finiteMatrixProduct n lower diagonal) lowerT))
        (finiteMatrixEqv_trans
          (finiteMatrixProduct_congr
            (finiteMatrixEqv_refl n lowerInvT) hmiddle)
          hlowerInvTLowerT)
    intro row column hrow hcolumn
    exact Q'.eqv_trans _ _ _
      ((finiteMatrixProduct_congr
        (finiteMatrixEqv_refl n inverse) hmatrix) hrow hcolumn)
      (hfactor hrow hcolumn)

/-- The explicit inverse factor is itself positive LDL data: its lower factor
is `L⁻ᵀ` and its diagonal consists of the positive reciprocal pivots. -/
def finiteMatrixInversePositiveLDLData
    {n : Nat} {matrix : Nat → Nat → Q'}
    (data : PositiveLDLData n matrix)
    (lowerInverse : UnitLowerInverseData n data.lower) :
    PositiveLDLData n
      (finiteMatrixInverseDataOfPositiveLDL data lowerInverse).inverse where
  lower := finiteMatrixTranspose lowerInverse.inverse
  diagonal := positiveDiagonalReciprocal
    n data.diagonal data.diagonal_pos
  entries := by
    intro row column hrow hcolumn
    let lowerInv := lowerInverse.inverse
    let lowerInvT := finiteMatrixTranspose lowerInv
    let diagonalInv := positiveDiagonalReciprocal
      n data.diagonal data.diagonal_pos
    change finiteMatrixProduct n lowerInvT
        (finiteMatrixProduct n (finiteDiagonalMatrix diagonalInv) lowerInv)
        row column ≈
      finiteLDLGram n lowerInvT diagonalInv row column
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (finiteMatrixProduct_assoc n lowerInvT
          (finiteDiagonalMatrix diagonalInv) lowerInv hrow hcolumn))
      (Q'.eqv_symm
        (finiteLDLGram_eq_product
          n lowerInvT diagonalInv row column))
  diagonal_pos := by
    intro index hindex
    unfold positiveDiagonalReciprocal
    rw [dif_pos hindex]
    exact Q'.recipPos_pos _ _

/-- Canonical all-dimension constructive inverse data for a symmetric strictly
positive rational matrix. -/
def finiteMatrixInverseDataOfStrictPositive
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixInverseData n matrix :=
  finiteMatrixInverseDataOfPositiveLDL
    (positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive)
    (positiveLDLLowerInverseData n matrix hsymmetric hpositive)

/-- Canonical positive LDL data for the exact inverse of a symmetric strictly
positive rational matrix. -/
def finiteMatrixInversePositiveLDLDataOfStrictPositive
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    PositiveLDLData n
      (finiteMatrixInverseDataOfStrictPositive
        n matrix hsymmetric hpositive).inverse :=
  finiteMatrixInversePositiveLDLData
    (positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive)
    (positiveLDLLowerInverseData n matrix hsymmetric hpositive)

/-- The canonical constructive inverse of a symmetric strictly positive
rational matrix is itself strictly positive.  The proof uses the explicit
inverse of the produced unit-lower factor: a nonzero coefficient vector has a
nonzero transformed channel, whose positive reciprocal pivot contributes a
strictly positive square. -/
theorem finiteMatrixInverseDataOfStrictPositive_strictlyPositive
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixStrictlyPositive n
      (finiteMatrixInverseDataOfStrictPositive
        n matrix hsymmetric hpositive).inverse := by
  intro coefficient selected hselected hcoefficient
  let precisionLDL :=
    positiveLDLDataOfStrictPositive n matrix hsymmetric hpositive
  let lowerInverse :=
    positiveLDLLowerInverseData n matrix hsymmetric hpositive
  let covarianceLDL :=
    finiteMatrixInversePositiveLDLData precisionLDL lowerInverse
  let transformed := fun channel =>
    finiteMatrixVectorApply n lowerInverse.inverse coefficient channel
  have hrecover :
      finiteMatrixVectorApply n precisionLDL.lower transformed selected ≈
        coefficient selected := by
    refine Q'.eqv_trans _
      (finiteMatrixVectorApply n
        (finiteMatrixProduct n precisionLDL.lower lowerInverse.inverse)
        coefficient selected) _
      (finiteMatrixVectorApply_product n precisionLDL.lower
        lowerInverse.inverse coefficient hselected) ?_
    exact Q'.eqv_trans _
      (finiteMatrixVectorApply n finiteIdentityMatrix coefficient selected) _
      (finiteMatrixVectorApply_congr lowerInverse.lower_inverse
        coefficient hselected)
      (finiteIdentityMatrix_vectorApply n coefficient hselected)
  have hsumNonzero :
      ¬ finiteMatrixVectorApply n precisionLDL.lower transformed selected ≈
        0 := by
    intro hzero
    exact hcoefficient
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hrecover) hzero)
  let witness := listQSumNonzeroWitness
    (fun channel => precisionLDL.lower selected channel * transformed channel)
    (List.range n) hsumNonzero
  have hwitness : witness.1 < n := List.mem_range.mp witness.2.1
  have htransformed : ¬ transformed witness.1 ≈ 0 := by
    intro hzero
    exact witness.2.2
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hzero)
        (Q'.mul_zero_eqv _))
  have hchannel :
      channelLinear (List.range n) covarianceLDL.lower
          coefficient witness.1 ≈
        transformed witness.1 := by
    change channelLinear (List.range n)
        (finiteMatrixTranspose lowerInverse.inverse)
        coefficient witness.1 ≈
      finiteMatrixVectorApply n lowerInverse.inverse coefficient witness.1
    exact channelLinear_transpose_eq_vectorApply
      n lowerInverse.inverse coefficient witness.1
  have hchannelNonzero :
      ¬ channelLinear (List.range n) covarianceLDL.lower
          coefficient witness.1 ≈ 0 := by
    intro hzero
    exact htransformed
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hchannel) hzero)
  have hchannelSquare :
      (0 : Q') <
        channelLinear (List.range n) covarianceLDL.lower
            coefficient witness.1 *
          channelLinear (List.range n) covarianceLDL.lower
            coefficient witness.1 :=
    positive_of_nonnegative_not_eqv_zero_local
      (SumOfSquares.q_mul_self_nonneg
        (channelLinear (List.range n) covarianceLDL.lower
          coefficient witness.1))
      (square_not_eqv_zero_local hchannelNonzero)
  have hwitnessTerm :
      (0 : Q') < covarianceLDL.diagonal witness.1 *
        (channelLinear (List.range n) covarianceLDL.lower
            coefficient witness.1 *
          channelLinear (List.range n) covarianceLDL.lower
            coefficient witness.1) :=
    Q'.mul_pos (covarianceLDL.diagonal_pos hwitness) hchannelSquare
  have hsos :
      (0 : Q') <
        weightedGramSOS (List.range n) (List.range n)
          covarianceLDL.diagonal covarianceLDL.lower coefficient := by
    unfold weightedGramSOS
    exact listQSum_positive_of_mem
      (fun channel => covarianceLDL.diagonal channel *
        (channelLinear (List.range n) covarianceLDL.lower coefficient channel *
          channelLinear (List.range n) covarianceLDL.lower coefficient channel))
      (List.range n)
      (fun channel hchannelMem =>
        Q'.mul_nonneg _ _
          (Q'.le_of_lt
            (covarianceLDL.diagonal_pos
              (List.mem_range.mp hchannelMem)))
          (SumOfSquares.q_mul_self_nonneg
            (channelLinear (List.range n) covarianceLDL.lower
              coefficient channel)))
      witness.2.1 hwitnessTerm
  have hquadraticToSOS :
      finiteMatrixQuadratic n
          (finiteMatrixInverseDataOfStrictPositive
            n matrix hsymmetric hpositive).inverse coefficient ≈
        weightedGramSOS (List.range n) (List.range n)
          covarianceLDL.diagonal covarianceLDL.lower coefficient := by
    exact Q'.eqv_trans _ _ _
      (finiteMatrixQuadratic_eq_weightedGram covarianceLDL.entries coefficient)
      (weightedGramQuadratic_eq_sos
        (List.range n) (List.range n)
        covarianceLDL.diagonal covarianceLDL.lower coefficient)
  exact Q'.pos_of_lt_of_le hsos
    (Q'.le_of_eqv (Q'.eqv_symm hquadraticToSOS))

/-- The canonical inverse passes the existing executable two-sided checker. -/
theorem finiteMatrixInverseDataOfStrictPositive_check
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    finiteMatrixInverseCheck n matrix
        (finiteMatrixInverseDataOfStrictPositive
          n matrix hsymmetric hpositive).inverse = true :=
  (finiteMatrixInverseDataOfStrictPositive
    n matrix hsymmetric hpositive).finiteMatrixInverseCheck_eq_true

end YMGap.Continuum.FiniteRationalPositiveDefiniteInverse

#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInverseDataOfPositiveLDL
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInversePositiveLDLData
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInverseDataOfStrictPositive
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInversePositiveLDLDataOfStrictPositive
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInverseDataOfStrictPositive_strictlyPositive
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteInverse.finiteMatrixInverseDataOfStrictPositive_check
