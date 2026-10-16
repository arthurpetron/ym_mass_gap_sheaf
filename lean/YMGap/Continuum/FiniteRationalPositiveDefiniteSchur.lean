/-
# Constructive Schur pullback of a positive rational matrix

For a strictly positive `(n+1)`-coordinate rational quadratic form, eliminate
its head coordinate by the explicit graph

    x_0 = -sum_j A(0,j+1) x_(j+1) / A(0,0).

The resulting `n`-coordinate matrix is defined literally as the pullback of
the original matrix along that graph.  Its strict positivity follows directly
from the already checked finite pullback identity because every tail
coordinate is recovered unchanged.  This is the recursive positivity step
needed by the all-scale LDL producer; the remaining factor-assembly theorem
must identify this pullback with the ordinary Schur entries and prepend the
positive head pivot.

This file constructs no inverse and makes no Gaussian-law, continuum, or
mass-gap claim.
-/

import YMGap.Constructive.Sqrt
import YMGap.Continuum.FiniteRationalMatrixPullback
import YMGap.Continuum.FiniteRationalPositiveDefiniteLDL

namespace YMGap.Continuum.FiniteRationalPositiveDefiniteSchur

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalMatrixPullback
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
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

/-- The positive head pivot supplied by strict positivity. -/
theorem headPivot_positive
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix) :
    (0 : Q') < matrix 0 0 :=
  finiteMatrixStrictlyPositive_diagonal hpositive (by omega)

/-- Generic graph embedding with an arbitrary head row and unchanged tail
coordinates. -/
def headGraphTransform
    (head : Nat → Q') (fullIndex reducedIndex : Nat) : Q' :=
  if fullIndex = 0 then head reducedIndex
  else if fullIndex = reducedIndex + 1 then 1 else 0

/-- Head coefficient of the rational elimination graph. -/
def headEliminationCoefficient
    (matrix : Nat → Nat → Q') (pivotInverse : Q')
    (reducedIndex : Nat) : Q' :=
  -(matrix 0 (reducedIndex + 1) * pivotInverse)

/-- Explicit graph transform used for one constructive Schur step.  Tail
coordinates are embedded unchanged; only the head coordinate is altered. -/
def headEliminationTransform
    (n : Nat) (matrix : Nat → Nat → Q')
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (fullIndex reducedIndex : Nat) : Q' :=
  headGraphTransform
    (headEliminationCoefficient matrix
      (Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)))
    fullIndex reducedIndex

/-- The reduced Schur matrix as the literal pullback along the elimination
graph. -/
def finiteSchurPullback
    (n : Nat) (matrix : Nat → Nat → Q')
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix) :
    Nat → Nat → Q' :=
  finiteMatrixPullback (n + 1) matrix
    (headEliminationTransform n matrix hpositive)

/-- A finite sum against a graph column has exactly its head contribution and
one selected tail contribution. -/
theorem listQSum_mul_headGraphTransform
    (n : Nat) (head : Nat → Q') (value : Nat → Q')
    {reducedIndex : Nat} (hindex : reducedIndex < n) :
    listQSum
        (fun fullIndex =>
          value fullIndex * headGraphTransform head fullIndex reducedIndex)
        (List.range (n + 1)) ≈
      value 0 * head reducedIndex + value (reducedIndex + 1) := by
  rw [List.range_succ_eq_map]
  simp only [listQSum, headGraphTransform, if_pos]
  rw [listQSum_map_local]
  refine Q'.add_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun index => if reducedIndex = index then value (index + 1) else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hmem
    have hnotZero : index + 1 ≠ 0 := by omega
    rw [if_neg hnotZero]
    by_cases heq : reducedIndex = index
    · subst index
      rw [if_pos rfl, if_pos rfl]
      exact Q'.mul_one_eqv _
    · have hsucc : index + 1 ≠ reducedIndex + 1 := by omega
      rw [if_neg hsucc, if_neg heq]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single reducedIndex
      (fun index => value (index + 1)) (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hindex)

/-- Entry formula for a matrix pulled back along an arbitrary head graph.  The
double finite sum reduces to the four expected head/tail terms. -/
theorem finiteMatrixPullback_headGraphTransform_entry
    (n : Nat) (matrix : Nat → Nat → Q') (head : Nat → Q')
    {left right : Nat} (hleft : left < n) (hright : right < n) :
    finiteMatrixPullback (n + 1) matrix (headGraphTransform head) left right ≈
      (matrix 0 0 * head right + matrix 0 (right + 1)) * head left +
        (matrix (left + 1) 0 * head right +
          matrix (left + 1) (right + 1)) := by
  unfold finiteMatrixPullback
  refine Q'.eqv_trans _
    (listQSum
      (fun i => headGraphTransform head i left *
        listQSum
          (fun j => matrix i j * headGraphTransform head j right)
          (List.range (n + 1)))
      (List.range (n + 1))) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j => headGraphTransform head i left *
          (matrix i j * headGraphTransform head j right))
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv (matrix i j)
            (headGraphTransform head i left)
            (headGraphTransform head j right)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv (matrix i j)
              (headGraphTransform head i left)))
          (Q'.mul_assoc_eqv (headGraphTransform head i left)
            (matrix i j) (headGraphTransform head j right)))
    · exact listQSum_mul_left
        (headGraphTransform head i left)
        (fun j => matrix i j * headGraphTransform head j right)
        (List.range (n + 1))
  · refine Q'.eqv_trans _
      (listQSum
        (fun i =>
          (listQSum
            (fun j => matrix i j * headGraphTransform head j right)
            (List.range (n + 1))) * headGraphTransform head i left)
        (List.range (n + 1))) _ ?_ ?_
    · apply listQSum_congr_on
      intro i _hi
      exact Q'.mul_comm_eqv _ _
    · refine Q'.eqv_trans _
        ((listQSum
            (fun j => matrix 0 j * headGraphTransform head j right)
            (List.range (n + 1))) * head left +
          listQSum
            (fun j => matrix (left + 1) j *
              headGraphTransform head j right)
            (List.range (n + 1))) _
        (listQSum_mul_headGraphTransform n head
          (fun i => listQSum
            (fun j => matrix i j * headGraphTransform head j right)
            (List.range (n + 1))) hleft) ?_
      exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ _
          (listQSum_mul_headGraphTransform n head (matrix 0) hright))
        (listQSum_mul_headGraphTransform n head
          (matrix (left + 1)) hright)

private theorem pivot_mul_eliminationHead_add_eqv_zero
    (pivot entry : Q') (hpivot : (0 : Q') < pivot) :
    pivot * (-(entry * Q'.recipPos pivot hpivot)) + entry ≈ 0 := by
  have hproduct :
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
  have hnegative :
      pivot * (-(entry * Q'.recipPos pivot hpivot)) ≈ -entry := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_neg_eqv pivot (entry * Q'.recipPos pivot hpivot))
      (Q'.neg_eqv_congr _ _ hproduct)
  exact Q'.eqv_trans _ (-entry + entry) _
    (Q'.add_eqv_congr_right _ _ _ hnegative)
    (Q'.neg_add_self_eqv entry)

/-- The pullback entry is the ordinary exact Schur complement entry. -/
theorem finiteSchurPullback_entry
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    {left right : Nat} (hleft : left < n) (hright : right < n) :
    finiteSchurPullback n matrix hpositive left right ≈
      matrix (left + 1) (right + 1) +
        -(matrix (left + 1) 0 *
          (matrix 0 (right + 1) *
            Q'.recipPos (matrix 0 0) (headPivot_positive hpositive))) := by
  unfold finiteSchurPullback headEliminationTransform
  let reciprocal :=
    Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)
  let head := headEliminationCoefficient matrix reciprocal
  have hfour := finiteMatrixPullback_headGraphTransform_entry
    n matrix head hleft hright
  refine Q'.eqv_trans _ _ _ hfour ?_
  have hcancel :
      matrix 0 0 * head right + matrix 0 (right + 1) ≈ 0 := by
    unfold head headEliminationCoefficient reciprocal
    exact pivot_mul_eliminationHead_add_eqv_zero
      (matrix 0 0) (matrix 0 (right + 1))
      (headPivot_positive hpositive)
  have hfirst :
      (matrix 0 0 * head right + matrix 0 (right + 1)) * head left ≈
        0 := by
    exact Q'.eqv_trans _ (0 * head left) _
      (Q'.mul_eqv_congr_right _ _ _ hcancel)
      (Q'.zero_mul_eqv _)
  have hsecond :
      matrix (left + 1) 0 * head right +
          matrix (left + 1) (right + 1) ≈
        matrix (left + 1) (right + 1) +
          -(matrix (left + 1) 0 *
            (matrix 0 (right + 1) * reciprocal)) := by
    unfold head headEliminationCoefficient
    exact Q'.eqv_trans _
      (-(matrix (left + 1) 0 *
          (matrix 0 (right + 1) * reciprocal)) +
        matrix (left + 1) (right + 1)) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_neg_eqv (matrix (left + 1) 0)
          (matrix 0 (right + 1) * reciprocal)))
      (Q'.add_comm_eqv _ _)
  exact Q'.eqv_trans _
    (0 + (matrix (left + 1) (right + 1) +
      -(matrix (left + 1) 0 *
        (matrix 0 (right + 1) * reciprocal)))) _
    (Q'.add_eqv_congr' hfirst hsecond)
    (Q'.eqv_of_eq (Q'.zero_add' _))

/-- The Schur pullback of an in-range symmetric matrix remains symmetric. -/
theorem finiteSchurPullback_symmetric
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (hsymmetric : FiniteMatrixSymmetric (n + 1) matrix) :
    FiniteMatrixSymmetric n (finiteSchurPullback n matrix hpositive) := by
  intro left right hleft hright
  let reciprocal :=
    Q'.recipPos (matrix 0 0) (headPivot_positive hpositive)
  have hmain :
      matrix (left + 1) (right + 1) ≈
        matrix (right + 1) (left + 1) :=
    hsymmetric (by omega) (by omega)
  have hleftHead : matrix (left + 1) 0 ≈ matrix 0 (left + 1) :=
    hsymmetric (by omega) (by omega)
  have hrightHead : matrix (right + 1) 0 ≈ matrix 0 (right + 1) :=
    hsymmetric (by omega) (by omega)
  have hcross :
      matrix (left + 1) 0 *
          (matrix 0 (right + 1) * reciprocal) ≈
        matrix (right + 1) 0 *
          (matrix 0 (left + 1) * reciprocal) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hleftHead)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            (matrix 0 (left + 1))
            (matrix 0 (right + 1)) reciprocal))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _
            (Q'.mul_comm_eqv
              (matrix 0 (left + 1)) (matrix 0 (right + 1))))
          (Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv
              (matrix 0 (right + 1))
              (matrix 0 (left + 1)) reciprocal)
            (Q'.mul_eqv_congr_right _ _ _
              (Q'.eqv_symm hrightHead)))))
  exact Q'.eqv_trans _ _ _
    (finiteSchurPullback_entry hpositive hleft hright)
    (Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr' hmain (Q'.neg_eqv_congr _ _ hcross))
      (Q'.eqv_symm
        (finiteSchurPullback_entry hpositive hright hleft)))

/-- Every tail coordinate is recovered unchanged by the elimination graph. -/
theorem finiteLinearApply_headEliminationTransform_tail
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (coefficient : Nat → Q') {index : Nat} (hindex : index < n) :
    finiteLinearApply n (headEliminationTransform n matrix hpositive)
        coefficient (index + 1) ≈
      coefficient index := by
  unfold finiteLinearApply
  refine Q'.eqv_trans _
    (listQSum
      (fun reducedIndex =>
        if index = reducedIndex then coefficient reducedIndex else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro reducedIndex _hreduced
    have hnotZero : index + 1 ≠ 0 := by omega
    unfold headEliminationTransform headGraphTransform
    rw [if_neg hnotZero]
    by_cases heq : index = reducedIndex
    · subst reducedIndex
      rw [if_pos rfl, if_pos rfl]
      exact Q'.mul_one_eqv _
    · have hsucc : index + 1 ≠ reducedIndex + 1 := by omega
      rw [if_neg hsucc, if_neg heq]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single index coefficient (List.range n)
      (rangeNodupLocal n) (List.mem_range.mpr hindex)

private theorem finiteLinearApply_tail_not_eqv_zero
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix)
    (coefficient : Nat → Q') {index : Nat} (hindex : index < n)
    (hcoordinate : ¬ coefficient index ≈ 0) :
    ¬ finiteLinearApply n (headEliminationTransform n matrix hpositive)
        coefficient (index + 1) ≈ 0 := by
  intro hzero
  apply hcoordinate
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteLinearApply_headEliminationTransform_tail
        hpositive coefficient hindex))
    hzero

/-- Strict positivity survives one Schur elimination step constructively.
The proof uses only the exact pullback identity and unchanged tail coordinate,
not determinant existence or classical linear algebra. -/
theorem finiteSchurPullback_strictlyPositive
    {n : Nat} {matrix : Nat → Nat → Q'}
    (hpositive : FiniteMatrixStrictlyPositive (n + 1) matrix) :
    FiniteMatrixStrictlyPositive n
      (finiteSchurPullback n matrix hpositive) := by
  intro coefficient index hindex hcoordinate
  have hfull := hpositive
    (finiteLinearApply n (headEliminationTransform n matrix hpositive)
      coefficient)
    (index + 1) (by omega)
    (finiteLinearApply_tail_not_eqv_zero
      hpositive coefficient hindex hcoordinate)
  exact Q'.pos_of_lt_of_le hfull
    (Q'.ge_of_eqv
      (finiteMatrixQuadratic_pullback
        (n + 1) n matrix
        (headEliminationTransform n matrix hpositive) coefficient))

end YMGap.Continuum.FiniteRationalPositiveDefiniteSchur

#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.headPivot_positive
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.listQSum_mul_headGraphTransform
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.finiteMatrixPullback_headGraphTransform_entry
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.finiteSchurPullback_entry
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.finiteSchurPullback_symmetric
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.finiteLinearApply_headEliminationTransform_tail
#print axioms YMGap.Continuum.FiniteRationalPositiveDefiniteSchur.finiteSchurPullback_strictlyPositive
