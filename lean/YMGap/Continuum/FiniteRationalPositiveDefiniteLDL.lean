/-
# Constructive positive-definite rational LDL data

This module starts the all-scale producer behind the finite Gaussian
coordinate route.  It packages strict positivity of a complete finite rational
quadratic form, proves that every in-range diagonal entry is strictly positive,
and compiles exact positive LDL data into the existing kernel-rechecked Boolean
certificate.

The zero- and one-coordinate constructors are the base cases for the recursive
Schur-complement producer.  The immediate consumer is the comb-gauge spatial
precision in
`SU2QuaternionFiniteGaussianOpenCubeCombPositiveDefinite.lean`.

This file does not yet implement the recursive Schur step, construct an inverse,
or prove any Gaussian-law, continuum, or mass-gap statement.
-/

import YMGap.Continuum.FiniteRationalLDLCertificate

namespace YMGap.Continuum.FiniteRationalPositiveDefiniteLDL

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-- Strict positivity of an `n`-coordinate rational matrix quadratic, stated
with an explicit nonzero coordinate witness. -/
def FiniteMatrixStrictlyPositive
    (n : Nat) (matrix : Nat → Nat → Q') : Prop :=
  ∀ (coefficient : Nat → Q') (index : Nat), index < n →
    ¬ coefficient index ≈ 0 →
    (0 : Q') < finiteMatrixQuadratic n matrix coefficient

/-- Symmetry of the in-range finite matrix entries. -/
def FiniteMatrixSymmetric
    (n : Nat) (matrix : Nat → Nat → Q') : Prop :=
  ∀ {left right : Nat}, left < n → right < n →
    matrix left right ≈ matrix right left

/-- A single finite coordinate basis vector. -/
def finiteCoordinateUnit (selected index : Nat) : Q' :=
  if selected = index then 1 else 0

theorem rangeNodupLocal (n : Nat) : (List.range n).Nodup := by
  induction n with
  | zero => exact List.nodup_nil
  | succ k induction =>
      rw [List.range_succ]
      refine List.nodup_append.mpr
        ⟨induction, List.nodup_cons.mpr
          ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
      intro x hx y hy hxy
      have hyk : y = k := List.mem_singleton.mp hy
      rw [hxy, hyk] at hx
      exact absurd (List.mem_range.mp hx) (Nat.lt_irrefl k)

theorem listQSum_ite_single
    {A : Type} [DecidableEq A] (selected : A) (value : A → Q') :
    ∀ items : List A,
      items.Nodup → selected ∈ items →
      listQSum
          (fun item => if selected = item then value item else 0)
          items ≈
        value selected
  | [], _hnodup, hmem => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hmem => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst head
        simp only [listQSum]
        have htailZero :
            listQSum
                (fun item => if selected = item then value item else 0)
                tail ≈ 0 := by
          refine Q'.eqv_trans _
            (listQSum (fun _item => (0 : Q')) tail) _ ?_ ?_
          · apply listQSum_congr_on
            intro item hitem
            rw [if_neg]
            exact Q'.eqv_refl 0
            intro heq
            exact hparts.1 (heq ▸ hitem)
          · exact listQSum_zero tail
        exact Q'.eqv_trans _ (value selected + 0) _
          (Q'.add_eqv_congr_left _ _ _ htailZero)
          (Q'.eqv_of_eq (Q'.add_zero' _))
      · have hne : selected ≠ head := by
          intro heq
          subst head
          exact hparts.1 htail
        simp only [listQSum, if_neg hne]
        exact Q'.eqv_trans _ (0 + value selected) _
          (Q'.add_eqv_congr_left _ _ _
            (listQSum_ite_single selected value tail hparts.2 htail))
          (Q'.eqv_of_eq (Q'.zero_add' _))

/-- The complete finite quadratic evaluated on a coordinate unit is its
corresponding diagonal matrix entry. -/
theorem finiteMatrixQuadratic_coordinateUnit
    (n : Nat) (matrix : Nat → Nat → Q')
    (selected : Nat) (hselected : selected < n) :
    finiteMatrixQuadratic n matrix (finiteCoordinateUnit selected) ≈
      matrix selected selected := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i => if selected = i then matrix i selected else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          if selected = i then
            if selected = j then matrix i j else 0
          else 0)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      by_cases his : selected = i
      · rw [if_pos his]
        by_cases hjs : selected = j
        · rw [if_pos hjs]
          unfold finiteCoordinateUnit
          rw [if_pos his, if_pos hjs]
          refine Q'.eqv_trans _ (1 * matrix i j) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ _ (Q'.one_mul_eqv 1)
          · exact Q'.one_mul_eqv _
        · rw [if_neg hjs]
          unfold finiteCoordinateUnit
          rw [if_pos his, if_neg hjs]
          refine Q'.eqv_trans _ (0 * matrix i j) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ _ (Q'.mul_zero_eqv 1)
          · exact Q'.zero_mul_eqv _
      · rw [if_neg his]
        unfold finiteCoordinateUnit
        rw [if_neg his]
        refine Q'.eqv_trans _ (0 * matrix i j) _ ?_ ?_
        · exact Q'.mul_eqv_congr_right _ _ _ (Q'.zero_mul_eqv _)
        · exact Q'.zero_mul_eqv _
    · by_cases his : selected = i
      · simpa only [if_pos his] using
          (listQSum_ite_single selected (matrix i)
            (List.range n) (rangeNodupLocal n)
            (List.mem_range.mpr hselected))
      · simpa only [if_neg his] using
          (listQSum_zero (List.range n))
  · exact listQSum_ite_single selected
      (fun i => matrix i selected) (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hselected)

theorem finiteCoordinateUnit_selected_not_eqv_zero (selected : Nat) :
    ¬ finiteCoordinateUnit selected selected ≈ 0 := by
  unfold finiteCoordinateUnit
  rw [if_pos rfl]
  decide

/-- Strict positivity of the full quadratic forces every in-range diagonal
entry to be strictly positive.  This is the first pivot fact used by a Schur
recursion. -/
theorem finiteMatrixStrictlyPositive_diagonal
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive n matrix)
    {index : Nat} (hindex : index < n) :
    (0 : Q') < matrix index index := by
  have hunit := hpositive (finiteCoordinateUnit index) index hindex
    (finiteCoordinateUnit_selected_not_eqv_zero index)
  exact Q'.pos_of_lt_of_le hunit
    (Q'.le_of_eqv
      (finiteMatrixQuadratic_coordinateUnit n matrix index hindex))

/-- Type-level exact LDL data with strictly positive pivots.  Keeping this as
data avoids any proposition-level choice when the recursive producer is
completed. -/
structure PositiveLDLData
    (n : Nat) (matrix : Nat → Nat → Q') : Type where
  lower : Nat → Nat → Q'
  diagonal : Nat → Q'
  entries : ∀ {row column : Nat}, row < n → column < n →
    matrix row column ≈ finiteLDLGram n lower diagonal row column
  diagonal_pos : ∀ {index : Nat}, index < n →
    (0 : Q') < diagonal index

namespace PositiveLDLData

/-- Exact positive LDL data passes the repository's ordinary finite Boolean
LDL checker. -/
theorem finiteLDLCheck_eq_true
    {n : Nat} {matrix : Nat → Nat → Q'}
    (data : PositiveLDLData n matrix) :
    finiteLDLCheck n matrix data.lower data.diagonal = true := by
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · apply List.all_eq_true.mpr
    intro row hrow
    unfold finiteLDLRowCheck
    apply List.all_eq_true.mpr
    intro column hcolumn
    exact decide_eq_true
      (data.entries (List.mem_range.mp hrow) (List.mem_range.mp hcolumn))
  · unfold finiteLDLDiagonalCheck
    apply List.all_eq_true.mpr
    intro index hindex
    exact decide_eq_true
      (Q'.le_of_lt (data.diagonal_pos (List.mem_range.mp hindex)))

/-- Vacuous exact positive LDL data in dimension zero. -/
def zero (matrix : Nat → Nat → Q') : PositiveLDLData 0 matrix where
  lower := fun _ _ => 0
  diagonal := fun _ => 0
  entries := by intro row _column hrow; omega
  diagonal_pos := by intro index hindex; omega

/-- The one-dimensional positive LDL factor: `L=[1]`, `D=[matrix 0 0]`. -/
def one (matrix : Nat → Nat → Q')
    (hpositive : FiniteMatrixStrictlyPositive 1 matrix) :
    PositiveLDLData 1 matrix where
  lower := fun row column => if row = 0 ∧ column = 0 then 1 else 0
  diagonal := fun index => if index = 0 then matrix 0 0 else 0
  entries := by
    intro row column hrow hcolumn
    have hrowZero : row = 0 := by omega
    have hcolumnZero : column = 0 := by omega
    subst row
    subst column
    unfold finiteLDLGram
    change matrix 0 0 ≈ matrix 0 0 * (1 * 1) + 0
    exact Q'.eqv_symm
      (Q'.eqv_trans _ (matrix 0 0 * 1 + 0) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)))
        (Q'.eqv_trans _ (matrix 0 0 * 1) _
          (Q'.eqv_of_eq (Q'.add_zero' _))
          (Q'.mul_one_eqv _)))
  diagonal_pos := by
    intro index hindex
    have hindexZero : index = 0 := by omega
    subst index
    rw [if_pos rfl]
    exact finiteMatrixStrictlyPositive_diagonal hpositive (by decide)

theorem one_finiteLDLCheck_eq_true
    (matrix : Nat → Nat → Q')
    (hpositive : FiniteMatrixStrictlyPositive 1 matrix) :
    finiteLDLCheck 1 matrix (one matrix hpositive).lower
      (one matrix hpositive).diagonal = true :=
  (one matrix hpositive).finiteLDLCheck_eq_true

end PositiveLDLData

end YMGap.Continuum.FiniteRationalPositiveDefiniteLDL

#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDL.finiteMatrixQuadratic_coordinateUnit
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDL.finiteMatrixStrictlyPositive_diagonal
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDL.PositiveLDLData.finiteLDLCheck_eq_true
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteLDL.PositiveLDLData.one_finiteLDLCheck_eq_true
