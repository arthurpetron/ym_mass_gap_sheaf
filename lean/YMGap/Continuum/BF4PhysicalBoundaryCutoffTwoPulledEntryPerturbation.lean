/-
# Relative pulled-form perturbations from entrywise errors

The fixed cutoff-two vacuum carrier now has a verified positive pulled-weight
floor and an `l1`-to-diagonal coercivity estimate.  This module consumes those
facts.  A uniform entrywise kernel error gives a cleared relative matrix-form
error, and a uniform entrywise weight error gives a cleared relative diagonal
error.  Explicit rational budget comparisons against the positive floor then
remove the clearing factor.

These theorems control the same coefficient at two representation cutoffs.
The moving head-centered coefficients at those cutoffs are generally
different, so a separate recentering perturbation remains necessary before a
robust gap-persistence family can be inhabited.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation

set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledL1DiagonalControl
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoPulledStates : List Nat :=
  centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 0

def cutoffTwoPulledWeightAt
    (cutoff index : Nat) : Q' :=
  centralPhysicalFinitePulledWeight
    cutoffTwoHalfCoupling (by decide) 2 cutoff 0 index

def cutoffTwoPulledKernelAt
    (cutoff row column : Nat) : Q' :=
  centralPhysicalFinitePulledKernel
    cutoffTwoHalfCoupling (by decide) 2 cutoff 0 row column

def cutoffTwoPulledMatrixAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointQuadratic cutoffTwoPulledStates coefficient
    (cutoffTwoPulledKernelAt cutoff)

def cutoffTwoPulledDiagonalAt
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  listQSum
    (fun index =>
      (coefficient index * coefficient index) *
        cutoffTwoPulledWeightAt cutoff index)
    cutoffTwoPulledStates

theorem cutoffTwoPulledDiagonalAt_nonnegative
    (cutoff : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoPulledDiagonalAt cutoff coefficient := by
  unfold cutoffTwoPulledDiagonalAt
    cutoffTwoPulledWeightAt
  apply listQSum_nonnegative_on
  intro index _hindex
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (coefficient index))
    (centralPhysicalFinitePulledWeight_nonnegative
      cutoffTwoHalfCoupling (by decide) 2 cutoff 0 index)

/-! ## 1. Kernel entry errors -/

/-- Uniform entrywise comparison of two pulled normalized kernels on the
fixed cutoff-two vacuum component. -/
structure CutoffTwoPulledKernelEntryErrorAt
    (first later : Nat) (epsilon : Q') : Type where
  later_ge_floor : cutoffTwoPulledRowFloorAnchor ≤ later
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  entry_error : ∀ row column,
    row ∈ cutoffTwoPulledStates → column ∈ cutoffTwoPulledStates →
    Q'.abs
        (cutoffTwoPulledKernelAt first row column +
          (-cutoffTwoPulledKernelAt later row column)) ≤
      epsilon

namespace CutoffTwoPulledKernelEntryErrorAt

/-- Entrywise kernel error, cleared by the positive physical row floor, is
relative to the later pulled diagonal. -/
theorem cleared_matrix_error
    {first later : Nat} {epsilon : Q'}
    (error : CutoffTwoPulledKernelEntryErrorAt first later epsilon)
    (coefficient : Nat → Q') :
    cutoffTwoPulledUniformPositiveRowFloor *
        Q'.abs
          (cutoffTwoPulledMatrixAt first coefficient +
            (-cutoffTwoPulledMatrixAt later coefficient)) ≤
      (Q'.ofNat cutoffTwoPulledStates.length * epsilon) *
        cutoffTwoPulledDiagonalAt later coefficient := by
  let l1 := coefficientL1 cutoffTwoPulledStates coefficient
  let diagonal := cutoffTwoPulledDiagonalAt later coefficient
  have hfinite :
      Q'.abs
          (cutoffTwoPulledMatrixAt first coefficient +
            (-cutoffTwoPulledMatrixAt later coefficient)) ≤
        (l1 * l1) * epsilon := by
    unfold cutoffTwoPulledMatrixAt
    exact finiteJointQuadratic_abs_sub_le_square
      cutoffTwoPulledStates coefficient
      (cutoffTwoPulledKernelAt first)
      (cutoffTwoPulledKernelAt later)
      epsilon error.epsilon_nonnegative error.entry_error
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hfinite
    (Q'.le_of_lt cutoffTwoPulledUniformPositiveRowFloor_pos)
  have hcoercive :
      cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1) ≤
        Q'.ofNat cutoffTwoPulledStates.length * diagonal := by
    exact floor_mul_coefficientL1_square_le_length_mul_diagonal
      cutoffTwoPulledStates (cutoffTwoPulledWeightAt later)
      coefficient cutoffTwoPulledUniformPositiveRowFloor
      (Q'.le_of_lt cutoffTwoPulledUniformPositiveRowFloor_pos)
      (fun index hindex => by
        unfold cutoffTwoPulledWeightAt
        exact cutoffTwoPulledUniformPositiveRowFloor_le_weight
          error.later_ge_floor hindex)
  have hcoerciveScaled :
      (cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1)) * epsilon ≤
        (Q'.ofNat cutoffTwoPulledStates.length * diagonal) * epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoercive
      error.epsilon_nonnegative
  refine Q'.le_trans' _ _ _ hscaled ?_
  refine Q'.le_trans' _
    ((cutoffTwoPulledUniformPositiveRowFloor * (l1 * l1)) * epsilon) _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          cutoffTwoPulledUniformPositiveRowFloor (l1 * l1) epsilon))) ?_
  refine Q'.le_trans' _ _ _ hcoerciveScaled ?_
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((Q'.ofNat cutoffTwoPulledStates.length * epsilon) * diagonal) _
      (by
        refine Q'.eqv_trans _
          (Q'.ofNat cutoffTwoPulledStates.length *
            (diagonal * epsilon)) _
          (Q'.mul_assoc_eqv _ _ _) ?_
        refine Q'.eqv_trans _
          (Q'.ofNat cutoffTwoPulledStates.length *
            (epsilon * diagonal)) _
          (Q'.mul_eqv_congr_left _ _ _
            (Q'.mul_comm_eqv diagonal epsilon)) ?_
        exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
      (Q'.eqv_refl _))

/-- A rational entry budget small relative to the positive row floor removes
the clearing factor and gives the exact robust matrix-error term. -/
theorem matrix_error
    {first later : Nat} {epsilon matrixError : Q'}
    (error : CutoffTwoPulledKernelEntryErrorAt first later epsilon)
    (hbudget :
      Q'.ofNat cutoffTwoPulledStates.length * epsilon ≤
        matrixError * cutoffTwoPulledUniformPositiveRowFloor)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledMatrixAt first coefficient +
          (-cutoffTwoPulledMatrixAt later coefficient)) ≤
      matrixError * cutoffTwoPulledDiagonalAt later coefficient := by
  let diagonal := cutoffTwoPulledDiagonalAt later coefficient
  have hdiagonal0 : (0 : Q') ≤ diagonal :=
    cutoffTwoPulledDiagonalAt_nonnegative later coefficient
  have hcleared := error.cleared_matrix_error coefficient
  have hbudgetScaled :
      (Q'.ofNat cutoffTwoPulledStates.length * epsilon) * diagonal ≤
        (matrixError * cutoffTwoPulledUniformPositiveRowFloor) * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbudget hdiagonal0
  have hreorder :
      (matrixError * cutoffTwoPulledUniformPositiveRowFloor) * diagonal ≈
        cutoffTwoPulledUniformPositiveRowFloor *
          (matrixError * diagonal) := by
    refine Q'.eqv_trans _
      (matrixError *
        (cutoffTwoPulledUniformPositiveRowFloor * diagonal)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (matrixError *
        (diagonal * cutoffTwoPulledUniformPositiveRowFloor)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv
          cutoffTwoPulledUniformPositiveRowFloor diagonal)) ?_
    refine Q'.eqv_trans _
      ((matrixError * diagonal) *
        cutoffTwoPulledUniformPositiveRowFloor) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_comm_eqv _ _
  have hfinal :
      cutoffTwoPulledUniformPositiveRowFloor *
          Q'.abs
            (cutoffTwoPulledMatrixAt first coefficient +
              (-cutoffTwoPulledMatrixAt later coefficient)) ≤
        cutoffTwoPulledUniformPositiveRowFloor *
          (matrixError * diagonal) :=
    Q'.le_trans' _ _ _ hcleared
      (Q'.le_trans' _ _ _ hbudgetScaled (Q'.le_of_eqv hreorder))
  exact le_of_mul_le_mul_left_pos
    cutoffTwoPulledUniformPositiveRowFloor_pos hfinal

end CutoffTwoPulledKernelEntryErrorAt

/-! ## 2. Weight entry errors -/

structure CutoffTwoPulledWeightEntryErrorAt
    (first later : Nat) (epsilon : Q') : Type where
  later_ge_floor : cutoffTwoPulledRowFloorAnchor ≤ later
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  entry_error : ∀ index, index ∈ cutoffTwoPulledStates →
    Q'.abs
        (cutoffTwoPulledWeightAt first index +
          (-cutoffTwoPulledWeightAt later index)) ≤
      epsilon

namespace CutoffTwoPulledWeightEntryErrorAt

private theorem floor_mul_squareSum_le_diagonal
    {later : Nat} (hlater : cutoffTwoPulledRowFloorAnchor ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoPulledUniformPositiveRowFloor *
        listQSum
          (fun index => coefficient index * coefficient index)
          cutoffTwoPulledStates ≤
      cutoffTwoPulledDiagonalAt later coefficient := by
  unfold cutoffTwoPulledDiagonalAt
  refine Q'.le_trans' _
    (listQSum
      (fun index => cutoffTwoPulledUniformPositiveRowFloor *
        (coefficient index * coefficient index))
      cutoffTwoPulledStates) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.eqv_symm
        (listQSum_mul_left cutoffTwoPulledUniformPositiveRowFloor
          (fun index => coefficient index * coefficient index)
          cutoffTwoPulledStates))
  · apply listQSum_mono
    intro index hindex
    refine Q'.le_trans' _
      ((coefficient index * coefficient index) *
        cutoffTwoPulledUniformPositiveRowFloor) _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv cutoffTwoPulledUniformPositiveRowFloor
          (coefficient index * coefficient index))) ?_
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (cutoffTwoPulledUniformPositiveRowFloor_le_weight hlater hindex)
      (SumOfSquares.q_mul_self_nonneg (coefficient index))

theorem cleared_diagonal_error
    {first later : Nat} {epsilon : Q'}
    (error : CutoffTwoPulledWeightEntryErrorAt first later epsilon)
    (coefficient : Nat → Q') :
    cutoffTwoPulledUniformPositiveRowFloor *
        Q'.abs
          (cutoffTwoPulledDiagonalAt first coefficient +
            (-cutoffTwoPulledDiagonalAt later coefficient)) ≤
      epsilon * cutoffTwoPulledDiagonalAt later coefficient := by
  let square : Nat → Q' := fun index => coefficient index * coefficient index
  let squareSum := listQSum square cutoffTwoPulledStates
  let diagonal := cutoffTwoPulledDiagonalAt later coefficient
  have habsL1 : coefficientL1 cutoffTwoPulledStates square ≈ squareSum := by
    unfold coefficientL1 square squareSum
    apply listQSum_congr
    intro index
    exact Q'.eqv_trans _
      (Q'.abs (coefficient index) * Q'.abs (coefficient index)) _
      (YMGap.Continuum.RcQuadResidualClose.q_abs_mul_eqv
        (coefficient index) (coefficient index))
      (Q'.abs_mul_self_eqv (coefficient index))
  have hfinite :
      Q'.abs
          (cutoffTwoPulledDiagonalAt first coefficient +
            (-cutoffTwoPulledDiagonalAt later coefficient)) ≤
        squareSum * epsilon := by
    have hraw := finiteLinearForm_abs_sub_le_l1_on
      cutoffTwoPulledStates square
      (cutoffTwoPulledWeightAt first)
      (cutoffTwoPulledWeightAt later)
      epsilon error.entry_error
    unfold cutoffTwoPulledDiagonalAt
      cutoffTwoPulledWeightAt
    exact Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_right _ _ epsilon habsL1))
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hfinite
    (Q'.le_of_lt cutoffTwoPulledUniformPositiveRowFloor_pos)
  have hfloorSquare := floor_mul_squareSum_le_diagonal
    error.later_ge_floor coefficient
  have hfloorSquareScaled :
      (cutoffTwoPulledUniformPositiveRowFloor * squareSum) * epsilon ≤
        diagonal * epsilon :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hfloorSquare
      error.epsilon_nonnegative
  refine Q'.le_trans' _ _ _ hscaled ?_
  refine Q'.le_trans' _
    ((cutoffTwoPulledUniformPositiveRowFloor * squareSum) * epsilon) _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv
          cutoffTwoPulledUniformPositiveRowFloor squareSum epsilon))) ?_
  exact Q'.le_trans' _ _ _ hfloorSquareScaled
    (Q'.le_of_eqv (Q'.mul_comm_eqv diagonal epsilon))

theorem diagonal_error
    {first later : Nat} {epsilon diagonalError : Q'}
    (error : CutoffTwoPulledWeightEntryErrorAt first later epsilon)
    (hbudget :
      epsilon ≤ diagonalError * cutoffTwoPulledUniformPositiveRowFloor)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledDiagonalAt first coefficient +
          (-cutoffTwoPulledDiagonalAt later coefficient)) ≤
      diagonalError * cutoffTwoPulledDiagonalAt later coefficient := by
  let diagonal := cutoffTwoPulledDiagonalAt later coefficient
  have hdiagonal0 : (0 : Q') ≤ diagonal :=
    cutoffTwoPulledDiagonalAt_nonnegative later coefficient
  have hcleared := error.cleared_diagonal_error coefficient
  have hbudgetScaled : epsilon * diagonal ≤
      (diagonalError * cutoffTwoPulledUniformPositiveRowFloor) * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbudget hdiagonal0
  have hreorder :
      (diagonalError * cutoffTwoPulledUniformPositiveRowFloor) * diagonal ≈
        cutoffTwoPulledUniformPositiveRowFloor *
          (diagonalError * diagonal) := by
    refine Q'.eqv_trans _
      (diagonalError *
        (cutoffTwoPulledUniformPositiveRowFloor * diagonal)) _
      (Q'.mul_assoc_eqv _ _ _) ?_
    refine Q'.eqv_trans _
      (diagonalError *
        (diagonal * cutoffTwoPulledUniformPositiveRowFloor)) _
      (Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_comm_eqv
          cutoffTwoPulledUniformPositiveRowFloor diagonal)) ?_
    refine Q'.eqv_trans _
      ((diagonalError * diagonal) *
        cutoffTwoPulledUniformPositiveRowFloor) _
      (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
    exact Q'.mul_comm_eqv _ _
  have hfinal :
      cutoffTwoPulledUniformPositiveRowFloor *
          Q'.abs
            (cutoffTwoPulledDiagonalAt first coefficient +
              (-cutoffTwoPulledDiagonalAt later coefficient)) ≤
        cutoffTwoPulledUniformPositiveRowFloor *
          (diagonalError * diagonal) :=
    Q'.le_trans' _ _ _ hcleared
      (Q'.le_trans' _ _ _ hbudgetScaled (Q'.le_of_eqv hreorder))
  exact le_of_mul_le_mul_left_pos
    cutoffTwoPulledUniformPositiveRowFloor_pos hfinal

/-- Relative diagonal error gives the multiplicative inflation form consumed
by robust gap persistence. -/
theorem diagonal_inflation
    {first later : Nat} {epsilon diagonalError : Q'}
    (error : CutoffTwoPulledWeightEntryErrorAt first later epsilon)
    (hbudget :
      epsilon ≤ diagonalError * cutoffTwoPulledUniformPositiveRowFloor)
    (coefficient : Nat → Q') :
    cutoffTwoPulledDiagonalAt first coefficient ≤
      ((1 : Q') + diagonalError) *
        cutoffTwoPulledDiagonalAt later coefficient := by
  let firstDiagonal := cutoffTwoPulledDiagonalAt first coefficient
  let laterDiagonal := cutoffTwoPulledDiagonalAt later coefficient
  have hrelative := error.diagonal_error hbudget coefficient
  have hadd : firstDiagonal ≤ laterDiagonal + diagonalError * laterDiagonal :=
    Q'.le_trans' _ _ _
      (ExpNeg.le_add_of_abs_sub_le hrelative)
      (Q'.le_refl' _)
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((1 : Q') * laterDiagonal + diagonalError * laterDiagonal) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.eqv_symm (Q'.one_mul_eqv laterDiagonal)))
        (Q'.eqv_symm
          (Q'.add_mul_eqv (1 : Q') diagonalError laterDiagonal))))

end CutoffTwoPulledWeightEntryErrorAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation.CutoffTwoPulledKernelEntryErrorAt.cleared_matrix_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation.CutoffTwoPulledKernelEntryErrorAt.matrix_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation.CutoffTwoPulledWeightEntryErrorAt.cleared_diagonal_error
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation.CutoffTwoPulledWeightEntryErrorAt.diagonal_inflation
