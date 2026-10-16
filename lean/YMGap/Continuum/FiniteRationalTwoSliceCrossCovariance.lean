/-
# Constructive cross covariance for a two-slice rational history

For a symmetric strictly positive finite spatial precision `A`, the endpoint
cross block of the one-bond history covariance is the inverse of

    A^2 + 2 A = A (A + 2 I).

This leaf first constructs that cross precision as `A^T A + 2 A`, proves it
strictly positive, and applies the canonical constructive inverse producer.
The follow-on block identity identifies this inverse with the actual endpoint
block of the complete two-slice history covariance.

No spectral theorem, eigenvalue selection, classical choice, Gaussian law,
continuum limit, or mass-gap statement is used or proved.
-/

import YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalMatrixAlgebra
open YMGap.Continuum.FiniteRationalMatrixPullback
open YMGap.Continuum.FiniteRationalPositiveDefiniteInverse
open YMGap.Continuum.FiniteRationalPositiveDefiniteLDL
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2QuaternionFiniteGaussianFreeHistoryPrecision

local infix:50 " ≈ " => Q'.eqv

private theorem finiteMatrixQuadratic_add_local
    (n : Nat) (left right : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (fun i j => left i j + right i j) coefficient ≈
      finiteMatrixQuadratic n left coefficient +
        finiteMatrixQuadratic n right coefficient := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i =>
        listQSum
            (fun j =>
              (coefficient i * coefficient j) * left i j)
            (List.range n) +
          listQSum
            (fun j =>
              (coefficient i * coefficient j) * right i j)
            (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j =>
          (coefficient i * coefficient j) * left i j +
            (coefficient i * coefficient j) * right i j)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact Q'.mul_add_eqv _ _ _
    · exact listQSum_add _ _ (List.range n)
  · exact listQSum_add _ _ (List.range n)

private theorem finiteMatrixQuadratic_scale_local
    (n : Nat) (scale : Q') (matrix : Nat → Nat → Q')
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n
        (fun i j => scale * matrix i j) coefficient ≈
      scale * finiteMatrixQuadratic n matrix coefficient := by
  unfold finiteMatrixQuadratic
  refine Q'.eqv_trans _
    (listQSum
      (fun i => scale * listQSum
        (fun j => (coefficient i * coefficient j) * matrix i j)
        (List.range n))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i _hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j => scale *
          ((coefficient i * coefficient j) * matrix i j))
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      exact poly_identity_of_normal_eq
        (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
        (.mul (.var 2) (.mul (.mul (.var 0) (.var 1)) (.var 3)))
        (by decide) (fun
          | 0 => coefficient i
          | 1 => coefficient j
          | 2 => scale
          | _ => matrix i j)
    · exact listQSum_mul_left scale _ (List.range n)
  · exact listQSum_mul_left scale _ (List.range n)

private theorem finiteIdentityMatrixQuadratic_eq_squares
    (n : Nat) (coefficient : Nat → Q') :
    finiteMatrixQuadratic n finiteIdentityMatrix coefficient ≈
      listQSum (fun index => coefficient index * coefficient index)
        (List.range n) := by
  unfold finiteMatrixQuadratic finiteIdentityMatrix
  apply listQSum_congr_on
  intro i hi
  refine Q'.eqv_trans _
    (listQSum
      (fun j => if i = j then coefficient i * coefficient i else 0)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro j _hj
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl, if_pos rfl]
      exact Q'.mul_one_eqv _
    · rw [if_neg hij, if_neg hij]
      exact Q'.mul_zero_eqv _
  · exact listQSum_ite_single i
      (fun _ => coefficient i * coefficient i)
      (List.range n) (rangeNodupLocal n) hi

private theorem finiteIdentityMatrixQuadratic_nonnegative
    (n : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ finiteMatrixQuadratic n finiteIdentityMatrix coefficient := by
  have hsquares :
      (0 : Q') ≤
        listQSum (fun index => coefficient index * coefficient index)
          (List.range n) := by
    apply listQSum_nonnegative_on
    intro index _hindex
    exact SumOfSquares.q_mul_self_nonneg (coefficient index)
  exact Q'.le_trans' _ _ _ hsquares
    (Q'.ge_of_eqv
      (finiteIdentityMatrixQuadratic_eq_squares n coefficient))

private theorem finiteMatrixPullback_symmetric_local
    (n : Nat) (matrix : Nat → Nat → Q')
    (transform : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (left right : Nat) :
    finiteMatrixPullback n matrix transform left right ≈
      finiteMatrixPullback n matrix transform right left := by
  unfold finiteMatrixPullback
  refine Q'.eqv_trans _
    (listQSum
      (fun j => listQSum
        (fun i => matrix i j *
          (transform i left * transform j right))
        (List.range n))
      (List.range n)) _
    (Q'.eqv_symm (listQSum_swap
      (fun i j => matrix i j *
        (transform i left * transform j right))
      (List.range n) (List.range n))) ?_
  apply listQSum_congr_on
  intro j hj
  apply listQSum_congr_on
  intro i hi
  refine Q'.eqv_trans _
    (matrix j i * (transform i left * transform j right)) _
    (Q'.mul_eqv_congr_right _ _ _
      (hsymmetric (List.mem_range.mp hi) (List.mem_range.mp hj))) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.mul_comm_eqv _ _)

private theorem finiteIdentityMatrix_symmetric_local (n : Nat) :
    FiniteMatrixSymmetric n finiteIdentityMatrix := by
  intro left right _hleft _hright
  exact Q'.eqv_of_eq (finiteIdentityMatrix_transpose left right).symm

/-- The finite cross precision `A^T A + 2 A`.  For symmetric `A` this is
`A^2 + 2 A = A (A + 2 I)`. -/
def twoSliceCrossPrecision
    (n : Nat) (matrix : Nat → Nat → Q')
    (left right : Nat) : Q' :=
  finiteMatrixPullback n finiteIdentityMatrix matrix left right +
    2 * matrix left right

/-- Symmetry of the cross precision inherited from symmetry of `A`. -/
theorem twoSliceCrossPrecision_symmetric
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix) :
    FiniteMatrixSymmetric n (twoSliceCrossPrecision n matrix) := by
  intro left right _hleft _hright
  unfold twoSliceCrossPrecision
  exact Q'.add_eqv_congr'
    (finiteMatrixPullback_symmetric_local n finiteIdentityMatrix
      matrix (finiteIdentityMatrix_symmetric_local n) left right)
    (Q'.mul_eqv_congr_left 2 _ _
      (hsymmetric _hleft _hright))

/-- Strict positivity of `A^T A + 2 A`: the Gram-square term is
nonnegative and the doubled original quadratic is strictly positive. -/
theorem twoSliceCrossPrecision_strictlyPositive
    (n : Nat) (matrix : Nat → Nat → Q')
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixStrictlyPositive n (twoSliceCrossPrecision n matrix) := by
  intro coefficient index hindex hcoordinate
  have hgramPullback := finiteMatrixQuadratic_pullback
    n n finiteIdentityMatrix matrix coefficient
  have hgramNonnegative :
      (0 : Q') ≤
        finiteMatrixQuadratic n
          (finiteMatrixPullback n finiteIdentityMatrix matrix)
          coefficient := by
    exact Q'.le_trans' _ _ _
      (finiteIdentityMatrixQuadratic_nonnegative n
        (finiteLinearApply n matrix coefficient))
      (Q'.ge_of_eqv hgramPullback)
  have hmatrixPositive := hpositive coefficient index hindex hcoordinate
  have hscaledPositive :
      (0 : Q') <
        finiteMatrixQuadratic n (fun i j => 2 * matrix i j) coefficient := by
    exact Q'.pos_of_lt_of_le
      (Q'.mul_pos (by decide : (0 : Q') < 2) hmatrixPositive)
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (finiteMatrixQuadratic_scale_local n 2 matrix coefficient)))
  have hscaledLeSum :
      finiteMatrixQuadratic n (fun i j => 2 * matrix i j) coefficient ≤
        finiteMatrixQuadratic n
            (finiteMatrixPullback n finiteIdentityMatrix matrix) coefficient +
          finiteMatrixQuadratic n (fun i j => 2 * matrix i j) coefficient := by
    have h := Q'.add_le_add_right
      (0 : Q')
      (finiteMatrixQuadratic n
        (finiteMatrixPullback n finiteIdentityMatrix matrix) coefficient)
      (finiteMatrixQuadratic n (fun i j => 2 * matrix i j) coefficient)
      hgramNonnegative
    rwa [Q'.zero_add'] at h
  have hsumPositive :
      (0 : Q') <
        finiteMatrixQuadratic n
            (finiteMatrixPullback n finiteIdentityMatrix matrix) coefficient +
          finiteMatrixQuadratic n (fun i j => 2 * matrix i j) coefficient :=
    Q'.pos_of_lt_of_le hscaledPositive hscaledLeSum
  exact Q'.pos_of_lt_of_le hsumPositive
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteMatrixQuadratic_add_local n
          (finiteMatrixPullback n finiteIdentityMatrix matrix)
          (fun i j => 2 * matrix i j) coefficient)))

/-- Canonical exact inverse data for the two-slice cross precision. -/
def twoSliceCrossInverseData
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixInverseData n (twoSliceCrossPrecision n matrix) :=
  finiteMatrixInverseDataOfStrictPositive n
    (twoSliceCrossPrecision n matrix)
    (twoSliceCrossPrecision_symmetric n matrix hsymmetric)
    (twoSliceCrossPrecision_strictlyPositive n matrix hpositive)

/-- The cross precision inverse is strictly positive on every explicit
nonzero finite coefficient vector. -/
theorem twoSliceCrossInverse_strictlyPositive
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixStrictlyPositive n
      (twoSliceCrossInverseData n matrix hsymmetric hpositive).inverse :=
  finiteMatrixInverseDataOfStrictPositive_strictlyPositive n
    (twoSliceCrossPrecision n matrix)
    (twoSliceCrossPrecision_symmetric n matrix hsymmetric)
    (twoSliceCrossPrecision_strictlyPositive n matrix hpositive)

private theorem listQSum_append_local {A : Type} (value : A → Q') :
    ∀ left right : List A,
      listQSum value (left ++ right) ≈
        listQSum value left + listQSum value right
  | [], right => Q'.eqv_symm (QPoly.q_zero_add_eqv _)
  | head :: tail, right => by
      change value head + listQSum value (tail ++ right) ≈
        (value head + listQSum value tail) + listQSum value right
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_append_local value tail right))
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

/-- Literal `2 × 2` block matrix with square blocks of size `n`. -/
def twoByTwoBlock
    (n : Nat) (topLeft topRight bottomLeft bottomRight : Nat → Nat → Q')
    (row column : Nat) : Q' :=
  if row < n then
    if column < n then topLeft row column
    else topRight row (column - n)
  else
    if column < n then bottomLeft (row - n) column
    else bottomRight (row - n) (column - n)

private theorem finiteMatrixProduct_twoByTwoBlock_topLeft
    (n : Nat)
    (a b c d e f g h : Nat → Nat → Q')
    {row column : Nat} (hrow : row < n) (hcolumn : column < n) :
    finiteMatrixProduct (n + n)
        (twoByTwoBlock n a b c d) (twoByTwoBlock n e f g h)
        row column ≈
      finiteMatrixProduct n a e row column +
        finiteMatrixProduct n b g row column := by
  unfold finiteMatrixProduct
  rw [List.range_add]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local _ (List.range n)
      ((List.range n).map fun index => n + index)) ?_
  apply Q'.add_eqv_congr'
  · apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    simp only [twoByTwoBlock, if_pos hrow, if_pos hcolumn, if_pos hindexLt]
    exact Q'.eqv_refl _
  · rw [listQSum_map_local]
    apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    have hshift : ¬ n + index < n := by omega
    simp only [twoByTwoBlock, if_pos hrow, if_pos hcolumn, if_neg hshift,
      Nat.add_sub_cancel_left]
    exact Q'.eqv_refl _

private theorem finiteMatrixProduct_twoByTwoBlock_topRight
    (n : Nat)
    (a b c d e f g h : Nat → Nat → Q')
    {row column : Nat}
    (hrow : row < n) (hcolumnLower : n ≤ column)
    (hcolumnUpper : column < n + n) :
    finiteMatrixProduct (n + n)
        (twoByTwoBlock n a b c d) (twoByTwoBlock n e f g h)
        row column ≈
      finiteMatrixProduct n a f row (column - n) +
        finiteMatrixProduct n b h row (column - n) := by
  unfold finiteMatrixProduct
  rw [List.range_add]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local _ (List.range n)
      ((List.range n).map fun index => n + index)) ?_
  have hcolumn : ¬ column < n := Nat.not_lt_of_ge hcolumnLower
  have hcolumnSub : column - n < n := by omega
  apply Q'.add_eqv_congr'
  · apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    simp only [twoByTwoBlock, if_pos hrow, if_neg hcolumn, if_pos hindexLt]
    exact Q'.eqv_refl _
  · rw [listQSum_map_local]
    apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    have hshift : ¬ n + index < n := by omega
    simp only [twoByTwoBlock, if_pos hrow, if_neg hcolumn, if_neg hshift,
      Nat.add_sub_cancel_left]
    exact Q'.eqv_refl _

private theorem finiteMatrixProduct_twoByTwoBlock_bottomLeft
    (n : Nat)
    (a b c d e f g h : Nat → Nat → Q')
    {row column : Nat}
    (hrowLower : n ≤ row) (hrowUpper : row < n + n)
    (hcolumn : column < n) :
    finiteMatrixProduct (n + n)
        (twoByTwoBlock n a b c d) (twoByTwoBlock n e f g h)
        row column ≈
      finiteMatrixProduct n c e (row - n) column +
        finiteMatrixProduct n d g (row - n) column := by
  unfold finiteMatrixProduct
  rw [List.range_add]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local _ (List.range n)
      ((List.range n).map fun index => n + index)) ?_
  have hrow : ¬ row < n := Nat.not_lt_of_ge hrowLower
  have hrowSub : row - n < n := by omega
  apply Q'.add_eqv_congr'
  · apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    simp only [twoByTwoBlock, if_neg hrow, if_pos hcolumn, if_pos hindexLt]
    exact Q'.eqv_refl _
  · rw [listQSum_map_local]
    apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    have hshift : ¬ n + index < n := by omega
    simp only [twoByTwoBlock, if_neg hrow, if_pos hcolumn, if_neg hshift,
      Nat.add_sub_cancel_left]
    exact Q'.eqv_refl _

private theorem finiteMatrixProduct_twoByTwoBlock_bottomRight
    (n : Nat)
    (a b c d e f g h : Nat → Nat → Q')
    {row column : Nat}
    (hrowLower : n ≤ row) (hrowUpper : row < n + n)
    (hcolumnLower : n ≤ column) (hcolumnUpper : column < n + n) :
    finiteMatrixProduct (n + n)
        (twoByTwoBlock n a b c d) (twoByTwoBlock n e f g h)
        row column ≈
      finiteMatrixProduct n c f (row - n) (column - n) +
        finiteMatrixProduct n d h (row - n) (column - n) := by
  unfold finiteMatrixProduct
  rw [List.range_add]
  refine Q'.eqv_trans _ _ _
    (listQSum_append_local _ (List.range n)
      ((List.range n).map fun index => n + index)) ?_
  have hrow : ¬ row < n := Nat.not_lt_of_ge hrowLower
  have hcolumn : ¬ column < n := Nat.not_lt_of_ge hcolumnLower
  have hrowSub : row - n < n := by omega
  have hcolumnSub : column - n < n := by omega
  apply Q'.add_eqv_congr'
  · apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    simp only [twoByTwoBlock, if_neg hrow, if_neg hcolumn, if_pos hindexLt]
    exact Q'.eqv_refl _
  · rw [listQSum_map_local]
    apply listQSum_congr_on
    intro index hindex
    have hindexLt : index < n := List.mem_range.mp hindex
    have hshift : ¬ n + index < n := by omega
    simp only [twoByTwoBlock, if_neg hrow, if_neg hcolumn, if_neg hshift,
      Nat.add_sub_cancel_left]
    exact Q'.eqv_refl _

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

private theorem finiteMatrixProduct_add_left_local
    (n : Nat) (left right tail : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n (fun i j => left i j + right i j) tail)
      (fun i j => finiteMatrixProduct n left tail i j +
        finiteMatrixProduct n right tail i j) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct
  refine Q'.eqv_trans _
    (listQSum
      (fun index => left row index * tail index column +
        right row index * tail index column)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    exact Q'.add_mul_eqv _ _ _
  · exact listQSum_add _ _ (List.range n)

private theorem finiteMatrixProduct_add_right_local
    (n : Nat) (head left right : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n head (fun i j => left i j + right i j))
      (fun i j => finiteMatrixProduct n head left i j +
        finiteMatrixProduct n head right i j) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct
  refine Q'.eqv_trans _
    (listQSum
      (fun index => head row index * left index column +
        head row index * right index column)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    exact Q'.mul_add_eqv _ _ _
  · exact listQSum_add _ _ (List.range n)

private theorem finiteMatrixProduct_neg_left_local
    (n : Nat) (head tail : Nat → Nat → Q') :
    FiniteMatrixEqv n
      (finiteMatrixProduct n (fun i j => -(head i j)) tail)
      (fun i j => -(finiteMatrixProduct n head tail i j)) := by
  intro row column _hrow _hcolumn
  unfold finiteMatrixProduct
  refine Q'.eqv_trans _
    (listQSum
      (fun index => -(head row index * tail index column))
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro index _hindex
    exact Q'.neg_mul_eqv _ _
  · exact listQSum_neg_local _ (List.range n)

private theorem finiteMatrixPullback_identity_eq_product
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix) :
    FiniteMatrixEqv n
      (finiteMatrixPullback n finiteIdentityMatrix matrix)
      (finiteMatrixProduct n matrix matrix) := by
  intro left right hleft _hright
  unfold finiteMatrixPullback finiteMatrixProduct finiteIdentityMatrix
  refine Q'.eqv_trans _
    (listQSum
      (fun i => matrix i left * matrix i right)
      (List.range n)) _ ?_ ?_
  · apply listQSum_congr_on
    intro i hi
    refine Q'.eqv_trans _
      (listQSum
        (fun j => if i = j then matrix i left * matrix i right else 0)
        (List.range n)) _ ?_ ?_
    · apply listQSum_congr_on
      intro j _hj
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, if_pos rfl]
        exact Q'.one_mul_eqv _
      · rw [if_neg hij, if_neg hij]
        exact Q'.zero_mul_eqv _
    · exact listQSum_ite_single i
        (fun _ => matrix i left * matrix i right)
        (List.range n) (rangeNodupLocal n) hi
  · apply listQSum_congr_on
    intro index hindex
    exact Q'.mul_eqv_congr_right _ _ _
      (hsymmetric (List.mem_range.mp hindex) hleft)

/-- One endpoint diagonal block of the one-bond precision. -/
def twoSliceStepPrecision
    (matrix : Nat → Nat → Q') (left right : Nat) : Q' :=
  matrix left right + finiteIdentityMatrix left right

/-- The off-diagonal endpoint block `-I`. -/
def twoSliceOffDiagonalPrecision (left right : Nat) : Q' :=
  -(finiteIdentityMatrix left right)

private theorem twoSliceStep_square_sub_identity
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix) :
    FiniteMatrixEqv n
      (fun i j =>
        finiteMatrixProduct n
            (twoSliceStepPrecision matrix)
            (twoSliceStepPrecision matrix) i j +
          -(finiteIdentityMatrix i j))
      (twoSliceCrossPrecision n matrix) := by
  intro row column hrow hcolumn
  have houter := finiteMatrixProduct_add_left_local n
    matrix finiteIdentityMatrix (twoSliceStepPrecision matrix)
    (row := row) (column := column) hrow hcolumn
  have hmatrixPart := finiteMatrixProduct_add_right_local n matrix
    matrix finiteIdentityMatrix
    (row := row) (column := column) hrow hcolumn
  have hidentityPart := finiteMatrixProduct_add_right_local n finiteIdentityMatrix
    matrix finiteIdentityMatrix
    (row := row) (column := column) hrow hcolumn
  have hmatrixIdentity := finiteMatrix_mul_identity n matrix hrow hcolumn
  have hidentityMatrix := finiteIdentityMatrix_mul n matrix hrow hcolumn
  have hidentityIdentity :=
    finiteIdentityMatrix_mul n finiteIdentityMatrix hrow hcolumn
  have hexpand :
      finiteMatrixProduct n
          (twoSliceStepPrecision matrix)
          (twoSliceStepPrecision matrix) row column ≈
        (finiteMatrixProduct n matrix matrix row column + matrix row column) +
          (matrix row column + finiteIdentityMatrix row column) := by
    refine Q'.eqv_trans _ _ _ houter ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_trans _ _ _ hmatrixPart
        (Q'.add_eqv_congr' (Q'.eqv_refl _) hmatrixIdentity))
      (Q'.eqv_trans _ _ _ hidentityPart
        (Q'.add_eqv_congr' hidentityMatrix hidentityIdentity))
  have hcancel :
      ((finiteMatrixProduct n matrix matrix row column + matrix row column) +
          (matrix row column + finiteIdentityMatrix row column)) +
          -(finiteIdentityMatrix row column) ≈
        finiteMatrixProduct n matrix matrix row column +
          2 * matrix row column := by
    exact poly_identity_of_normal_eq
      (.add
        (.add (.add (.var 0) (.var 1)) (.add (.var 1) (.var 2)))
        (.neg (.var 2)))
      (.add (.var 0) (.mul (.const 2) (.var 1)))
      (by decide) (fun
        | 0 => finiteMatrixProduct n matrix matrix row column
        | 1 => matrix row column
        | _ => finiteIdentityMatrix row column)
  exact Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _ hexpand)
    (Q'.eqv_trans _ _ _ hcancel
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (finiteMatrixPullback_identity_eq_product
            n matrix hsymmetric hrow hcolumn))))

/-- Exact cross block used by the one-bond covariance candidate. -/
def twoSliceCrossCovariance
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    Nat → Nat → Q' :=
  (twoSliceCrossInverseData n matrix hsymmetric hpositive).inverse

/-- Exact endpoint diagonal block `(A+I)(A^2+2A)^{-1}`. -/
def twoSliceDiagonalCovariance
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    Nat → Nat → Q' :=
  finiteMatrixProduct n (twoSliceStepPrecision matrix)
    (twoSliceCrossCovariance n matrix hsymmetric hpositive)

private theorem twoSlice_diagonal_block_product
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixEqv n
      (fun i j =>
        finiteMatrixProduct n (twoSliceStepPrecision matrix)
            (twoSliceDiagonalCovariance n matrix hsymmetric hpositive) i j +
          finiteMatrixProduct n twoSliceOffDiagonalPrecision
            (twoSliceCrossCovariance n matrix hsymmetric hpositive) i j)
      finiteIdentityMatrix := by
  let cross := twoSliceCrossCovariance n matrix hsymmetric hpositive
  let diagonal := twoSliceDiagonalCovariance n matrix hsymmetric hpositive
  intro row column hrow hcolumn
  have hassoc := finiteMatrixProduct_assoc n
    (twoSliceStepPrecision matrix) (twoSliceStepPrecision matrix) cross
    hrow hcolumn
  have hoff := finiteMatrixProduct_neg_left_local n
    finiteIdentityMatrix cross hrow hcolumn
  have hidCross := finiteIdentityMatrix_mul n cross hrow hcolumn
  have hcombine := finiteMatrixProduct_add_left_local n
    (finiteMatrixProduct n (twoSliceStepPrecision matrix)
      (twoSliceStepPrecision matrix))
    (fun i j => -(finiteIdentityMatrix i j)) cross hrow hcolumn
  have hprecision :
      FiniteMatrixEqv n
        (fun i j =>
          finiteMatrixProduct n
              (twoSliceStepPrecision matrix)
              (twoSliceStepPrecision matrix) i j +
            -(finiteIdentityMatrix i j))
        (twoSliceCrossPrecision n matrix) :=
    twoSliceStep_square_sub_identity n matrix hsymmetric
  have hreplace := finiteMatrixProduct_congr hprecision
    (finiteMatrixEqv_refl n cross) hrow hcolumn
  have hinverse :=
    (twoSliceCrossInverseData n matrix hsymmetric hpositive).matrix_inverse
      hrow hcolumn
  have hoffCross :
      finiteMatrixProduct n twoSliceOffDiagonalPrecision cross row column ≈
        -(cross row column) :=
    Q'.eqv_trans _ _ _ hoff
      (Q'.neg_eqv_congr _ _ hidCross)
  change
    finiteMatrixProduct n (twoSliceStepPrecision matrix) diagonal row column +
        finiteMatrixProduct n twoSliceOffDiagonalPrecision cross row column ≈
      finiteIdentityMatrix row column
  refine Q'.eqv_trans _
    (finiteMatrixProduct n
        (finiteMatrixProduct n (twoSliceStepPrecision matrix)
          (twoSliceStepPrecision matrix)) cross row column +
      -(cross row column)) _ ?_ ?_
  · apply Q'.add_eqv_congr'
    · exact Q'.eqv_symm hassoc
    · exact hoffCross
  · refine Q'.eqv_trans _
      (finiteMatrixProduct n
        (fun i j =>
          finiteMatrixProduct n (twoSliceStepPrecision matrix)
              (twoSliceStepPrecision matrix) i j +
            -(finiteIdentityMatrix i j))
        cross row column) _ ?_ ?_
    · exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left _ _ _ (Q'.eqv_symm hoffCross))
        (Q'.eqv_symm hcombine)
    · exact Q'.eqv_trans _ _ _ hreplace hinverse

private theorem twoSlice_cross_block_product
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixEqv n
      (fun i j =>
        finiteMatrixProduct n (twoSliceStepPrecision matrix)
            (twoSliceCrossCovariance n matrix hsymmetric hpositive) i j +
          finiteMatrixProduct n twoSliceOffDiagonalPrecision
            (twoSliceDiagonalCovariance n matrix hsymmetric hpositive) i j)
      (fun _ _ => 0) := by
  let cross := twoSliceCrossCovariance n matrix hsymmetric hpositive
  let diagonal := twoSliceDiagonalCovariance n matrix hsymmetric hpositive
  intro row column hrow hcolumn
  have hoff := finiteMatrixProduct_neg_left_local n
    finiteIdentityMatrix diagonal hrow hcolumn
  have hidDiagonal := finiteIdentityMatrix_mul n diagonal hrow hcolumn
  change
    finiteMatrixProduct n (twoSliceStepPrecision matrix) cross row column +
        finiteMatrixProduct n twoSliceOffDiagonalPrecision diagonal row column ≈
      0
  exact Q'.eqv_trans _
    (diagonal row column + -(diagonal row column)) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.eqv_trans _ _ _ hoff
        (Q'.neg_eqv_congr _ _ hidDiagonal)))
    (Q'.add_neg_self_eqv _)

/-- The literal complete one-bond precision in `2 × 2` block form. -/
def twoSliceBlockPrecision
    (n : Nat) (matrix : Nat → Nat → Q') : Nat → Nat → Q' :=
  twoByTwoBlock n
    (twoSliceStepPrecision matrix) twoSliceOffDiagonalPrecision
    twoSliceOffDiagonalPrecision (twoSliceStepPrecision matrix)

/-- Explicit complete one-bond covariance candidate with the same cross block
at both endpoint orientations. -/
def twoSliceBlockCovariance
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    Nat → Nat → Q' :=
  twoByTwoBlock n
    (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
    (twoSliceCrossCovariance n matrix hsymmetric hpositive)
    (twoSliceCrossCovariance n matrix hsymmetric hpositive)
    (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)

/-- The literal one-bond free-history precision is exactly the two-slice block
precision once the flattened spatial coordinate size is positive. -/
theorem freeHistoryPrecision_one_eq_twoSliceBlock
    (n : Nat) (matrix : Nat → Nat → Q') (hsize : 0 < n) :
    FiniteMatrixEqv (n + n)
      (freeHistoryPrecision 1 n matrix)
      (twoSliceBlockPrecision n matrix) := by
  intro row column hrow hcolumn
  by_cases hrowTop : row < n
  · by_cases hcolumnTop : column < n
    · have hentry := freeHistoryPrecision_sameTime
        1 n matrix 0 row column hsize hrowTop hcolumnTop
      have hrowIndex : historyIndex n 0 row = row := by
        simp [historyIndex]
      have hcolumnIndex : historyIndex n 0 column = column := by
        simp [historyIndex]
      rw [hrowIndex, hcolumnIndex] at hentry
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hentry) (by
        simp [freeTemporalDegree, twoSliceBlockPrecision, twoByTwoBlock,
          twoSliceStepPrecision, finiteIdentityMatrix, hrowTop, hcolumnTop]
        exact Q'.eqv_refl _)
    · have hcolumnLower : n ≤ column := Nat.le_of_not_gt hcolumnTop
      have hcolumnSub : column - n < n := by omega
      have hentry := freeHistoryPrecision_adjacentTime
        1 n matrix 0 row (column - n) hsize hrowTop hcolumnSub
      have hrowIndex : historyIndex n 0 row = row := by
        simp [historyIndex]
      have hcolumnIndex : historyIndex n 1 (column - n) = column := by
        unfold historyIndex
        omega
      rw [hrowIndex, hcolumnIndex] at hentry
      exact Q'.eqv_trans _ _ _ hentry (by
        simp only [twoSliceBlockPrecision, twoByTwoBlock,
          twoSliceOffDiagonalPrecision, finiteIdentityMatrix,
          if_pos hrowTop, if_neg hcolumnTop]
        by_cases heq : row = column - n
        · rw [if_pos heq, if_pos heq]
          exact Q'.eqv_refl _
        · rw [if_neg heq, if_neg heq]
          decide)
  · have hrowLower : n ≤ row := Nat.le_of_not_gt hrowTop
    have hrowSub : row - n < n := by omega
    by_cases hcolumnTop : column < n
    · have hentry := freeHistoryPrecision_index
        1 n matrix 1 0 (row - n) column
        hsize hrowSub hcolumnTop
      have hrowIndex : historyIndex n 1 (row - n) = row := by
        unfold historyIndex
        omega
      have hcolumnIndex : historyIndex n 0 column = column := by
        simp [historyIndex]
      rw [hrowIndex, hcolumnIndex] at hentry
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hentry) (by
        simp [freeTemporalPrecision, twoSliceBlockPrecision, twoByTwoBlock,
          twoSliceOffDiagonalPrecision, finiteIdentityMatrix,
          hrowTop, hcolumnTop]
        by_cases heq : row - n = column
        · rw [if_pos heq, if_pos heq]
          decide
        · rw [if_neg heq, if_neg heq]
          decide)
    · have hcolumnLower : n ≤ column := Nat.le_of_not_gt hcolumnTop
      have hcolumnSub : column - n < n := by omega
      have hentry := freeHistoryPrecision_sameTime
        1 n matrix 1 (row - n) (column - n)
        hsize hrowSub hcolumnSub
      have hrowIndex : historyIndex n 1 (row - n) = row := by
        unfold historyIndex
        omega
      have hcolumnIndex : historyIndex n 1 (column - n) = column := by
        unfold historyIndex
        omega
      rw [hrowIndex, hcolumnIndex] at hentry
      exact Q'.eqv_trans _ _ _ (Q'.eqv_of_eq hentry) (by
        simp [freeTemporalDegree, twoSliceBlockPrecision, twoByTwoBlock,
          twoSliceStepPrecision, finiteIdentityMatrix,
          hrowTop, hcolumnTop]
        exact Q'.eqv_refl _)

/-- The explicit two-slice block covariance is a right inverse of the complete
one-bond block precision. -/
theorem twoSliceBlockCovariance_rightInverse
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix) :
    FiniteMatrixEqv (n + n)
      (finiteMatrixProduct (n + n)
        (twoSliceBlockPrecision n matrix)
        (twoSliceBlockCovariance n matrix hsymmetric hpositive))
      finiteIdentityMatrix := by
  intro row column hrow hcolumn
  by_cases hrowTop : row < n
  · by_cases hcolumnTop : column < n
    · exact Q'.eqv_trans _ _ _
        (finiteMatrixProduct_twoByTwoBlock_topLeft n
          (twoSliceStepPrecision matrix) twoSliceOffDiagonalPrecision
          twoSliceOffDiagonalPrecision (twoSliceStepPrecision matrix)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          hrowTop hcolumnTop)
        (twoSlice_diagonal_block_product n matrix hsymmetric hpositive
          hrowTop hcolumnTop)
    · have hcolumnLower : n ≤ column := Nat.le_of_not_gt hcolumnTop
      have hcolumnSub : column - n < n := by omega
      refine Q'.eqv_trans _ _ _
        (finiteMatrixProduct_twoByTwoBlock_topRight n
          (twoSliceStepPrecision matrix) twoSliceOffDiagonalPrecision
          twoSliceOffDiagonalPrecision (twoSliceStepPrecision matrix)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          hrowTop hcolumnLower hcolumn) ?_
      refine Q'.eqv_trans _ _ _
        (twoSlice_cross_block_product n matrix hsymmetric hpositive
          hrowTop hcolumnSub) ?_
      unfold finiteIdentityMatrix
      rw [if_neg (show row ≠ column by omega)]
      exact Q'.eqv_refl _
  · have hrowLower : n ≤ row := Nat.le_of_not_gt hrowTop
    have hrowSub : row - n < n := by omega
    by_cases hcolumnTop : column < n
    · refine Q'.eqv_trans _ _ _
        (finiteMatrixProduct_twoByTwoBlock_bottomLeft n
          (twoSliceStepPrecision matrix) twoSliceOffDiagonalPrecision
          twoSliceOffDiagonalPrecision (twoSliceStepPrecision matrix)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          hrowLower hrow hcolumnTop) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv _ _) ?_
      refine Q'.eqv_trans _ _ _
        (twoSlice_cross_block_product n matrix hsymmetric hpositive
          hrowSub hcolumnTop) ?_
      unfold finiteIdentityMatrix
      rw [if_neg (show row ≠ column by omega)]
      exact Q'.eqv_refl _
    · have hcolumnLower : n ≤ column := Nat.le_of_not_gt hcolumnTop
      have hcolumnSub : column - n < n := by omega
      refine Q'.eqv_trans _ _ _
        (finiteMatrixProduct_twoByTwoBlock_bottomRight n
          (twoSliceStepPrecision matrix) twoSliceOffDiagonalPrecision
          twoSliceOffDiagonalPrecision (twoSliceStepPrecision matrix)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceCrossCovariance n matrix hsymmetric hpositive)
          (twoSliceDiagonalCovariance n matrix hsymmetric hpositive)
          hrowLower hrow hcolumnLower hcolumn) ?_
      refine Q'.eqv_trans _ _ _
        (Q'.add_comm_eqv _ _) ?_
      refine Q'.eqv_trans _ _ _
        (twoSlice_diagonal_block_product n matrix hsymmetric hpositive
          hrowSub hcolumnSub) ?_
      unfold finiteIdentityMatrix
      by_cases heq : row = column
      · subst column
        rw [if_pos rfl, if_pos rfl]
        exact Q'.eqv_refl _
      · have hsub : row - n ≠ column - n := by omega
        rw [if_neg hsub, if_neg heq]
        exact Q'.eqv_refl _

private theorem finiteMatrixInverse_eq_rightInverse
    {n : Nat} {matrix candidate : Nat → Nat → Q'}
    (data : FiniteMatrixInverseData n matrix)
    (hright : FiniteMatrixEqv n
      (finiteMatrixProduct n matrix candidate) finiteIdentityMatrix) :
    FiniteMatrixEqv n data.inverse candidate := by
  have hinsert :
      FiniteMatrixEqv n
        (finiteMatrixProduct n data.inverse finiteIdentityMatrix)
        (finiteMatrixProduct n data.inverse
          (finiteMatrixProduct n matrix candidate)) :=
    finiteMatrixProduct_congr
      (finiteMatrixEqv_refl n data.inverse)
      (finiteMatrixEqv_symm hright)
  have hassoc :
      FiniteMatrixEqv n
        (finiteMatrixProduct n
          (finiteMatrixProduct n data.inverse matrix) candidate)
        (finiteMatrixProduct n data.inverse
          (finiteMatrixProduct n matrix candidate)) :=
    finiteMatrixProduct_assoc n data.inverse matrix candidate
  have hreplace :
      FiniteMatrixEqv n
        (finiteMatrixProduct n
          (finiteMatrixProduct n data.inverse matrix) candidate)
        (finiteMatrixProduct n finiteIdentityMatrix candidate) :=
    finiteMatrixProduct_congr data.inverse_matrix
      (finiteMatrixEqv_refl n candidate)
  intro row column hrow hcolumn
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (finiteMatrix_mul_identity n data.inverse hrow hcolumn))
    (Q'.eqv_trans _ _ _
      (hinsert hrow hcolumn)
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (hassoc hrow hcolumn))
        (Q'.eqv_trans _ _ _
          (hreplace hrow hcolumn)
          (finiteIdentityMatrix_mul n candidate hrow hcolumn))))

/-- Any exact two-sided inverse of the one-bond block precision has the
explicit covariance block form above. -/
theorem finiteMatrixInverse_eq_twoSliceBlockCovariance
    (n : Nat) (matrix : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix)
    (data : FiniteMatrixInverseData (n + n)
      (twoSliceBlockPrecision n matrix)) :
    FiniteMatrixEqv (n + n) data.inverse
      (twoSliceBlockCovariance n matrix hsymmetric hpositive) :=
  finiteMatrixInverse_eq_rightInverse data
    (twoSliceBlockCovariance_rightInverse n matrix hsymmetric hpositive)

/-- Entrywise identification of an arbitrary recorded precision with the
one-bond block precision transports its exact inverse to the explicit block
covariance. -/
theorem finiteMatrixInverse_eq_twoSliceBlockCovariance_of_precision
    (n : Nat) (matrix precision : Nat → Nat → Q')
    (hsymmetric : FiniteMatrixSymmetric n matrix)
    (hpositive : FiniteMatrixStrictlyPositive n matrix)
    (hprecision : FiniteMatrixEqv (n + n) precision
      (twoSliceBlockPrecision n matrix))
    (data : FiniteMatrixInverseData (n + n) precision) :
    FiniteMatrixEqv (n + n) data.inverse
      (twoSliceBlockCovariance n matrix hsymmetric hpositive) := by
  have hreplace :
      FiniteMatrixEqv (n + n)
        (finiteMatrixProduct (n + n) precision
          (twoSliceBlockCovariance n matrix hsymmetric hpositive))
        (finiteMatrixProduct (n + n) (twoSliceBlockPrecision n matrix)
          (twoSliceBlockCovariance n matrix hsymmetric hpositive)) :=
    finiteMatrixProduct_congr hprecision
      (finiteMatrixEqv_refl (n + n)
        (twoSliceBlockCovariance n matrix hsymmetric hpositive))
  have hright :
      FiniteMatrixEqv (n + n)
        (finiteMatrixProduct (n + n) precision
          (twoSliceBlockCovariance n matrix hsymmetric hpositive))
        finiteIdentityMatrix :=
    finiteMatrixEqv_trans hreplace
      (twoSliceBlockCovariance_rightInverse n matrix hsymmetric hpositive)
  exact (finiteMatrixInverse_eq_rightInverse data hright :
    FiniteMatrixEqv (n + n) data.inverse
      (twoSliceBlockCovariance n matrix hsymmetric hpositive))

end YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance

#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.twoSliceCrossPrecision_symmetric
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.twoSliceCrossPrecision_strictlyPositive
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.twoSliceCrossInverse_strictlyPositive
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.freeHistoryPrecision_one_eq_twoSliceBlock
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.twoSliceBlockCovariance_rightInverse
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.finiteMatrixInverse_eq_twoSliceBlockCovariance
#print axioms YMGap.Continuum.FiniteRationalTwoSliceCrossCovariance.finiteMatrixInverse_eq_twoSliceBlockCovariance_of_precision
