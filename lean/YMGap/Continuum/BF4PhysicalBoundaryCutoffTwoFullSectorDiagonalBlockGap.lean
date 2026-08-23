/-
# Diagonal-preserving old/new block gap compiler

For arbitrary vectors on a growing vacuum sector, the newly appearing block
cannot honestly be treated as a uniformly small part of the norm: a vector
may be supported entirely there.  The correct block contraction therefore
preserves the exact diagonal partition.

If the old-old and new-new quadratic blocks both contract at a common rate
`q` against their own diagonal pieces, while the sum of the two cross-block
absolute values is at most `c` times the full diagonal, then the entire
centered sector contracts at rate `q + c`.  In particular, the two diagonal
rates are not added.  This is the recursive form needed to propagate a gap
through genuinely new degrees of freedom.

A constructively cofinal family of these block certificates compiles to the
actual completed vacuum-sector transfer contraction.  No such cofinal family
is constructed here, and no thermodynamic, continuum, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoOldPulledDiagonal
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    cutoffTwoHalfCoupling (by decide) 2 later 0
    (cutoffTwoOldCoefficientPullback later coefficient)

def cutoffTwoDiagonalBlockRate (blockRate crossError : Q') : Q' :=
  blockRate + crossError

/-! ## 1. The exact diagonal partition is an ordered partition -/

theorem cutoffTwoOldPulledDiagonal_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoOldPulledDiagonal later coefficient := by
  unfold cutoffTwoOldPulledDiagonal
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
  apply listQSum_nonnegative_on
  intro index _hindex
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg
      (cutoffTwoOldCoefficientPullback later coefficient index))
    (centralPhysicalFinitePulledWeight_nonnegative
      cutoffTwoHalfCoupling (by decide) 2 later 0 index)

theorem cutoffTwoNewDiagonal_nonnegative
    (later : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoNewDiagonal later coefficient := by
  unfold cutoffTwoNewDiagonal
  apply listQSum_nonnegative_on
  intro index _hindex
  exact Q'.mul_nonneg _ _
    (SumOfSquares.q_mul_self_nonneg (coefficient index))
    (by
      unfold centralPhysicalFiniteWeight
      exact centralPhysicalRowMarginal_nonnegative
        (by decide) later 0 _)

/-- The old diagonal piece is bounded by the full diagonal because the
complementary new piece is nonnegative. -/
theorem cutoffTwoOldPulledDiagonal_le_full
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoOldPulledDiagonal later coefficient ≤
      cutoffTwoFullSectorDiagonal later coefficient := by
  have hsplit :=
    cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new
      hcutoff coefficient
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg _ _
      (cutoffTwoNewDiagonal_nonnegative later coefficient))
    (Q'.ge_of_eqv hsplit)

/-- The new diagonal piece is bounded by the full diagonal for the symmetric
reason. -/
theorem cutoffTwoNewDiagonal_le_full
    {later : Nat} (hcutoff : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoNewDiagonal later coefficient ≤
      cutoffTwoFullSectorDiagonal later coefficient := by
  have hsplit :=
    cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new
      hcutoff coefficient
  refine Q'.le_trans' _
    (cutoffTwoOldPulledDiagonal later coefficient +
      cutoffTwoNewDiagonal later coefficient) _ ?_ ?_
  · exact Q'.le_trans' _
      (cutoffTwoNewDiagonal later coefficient +
        cutoffTwoOldPulledDiagonal later coefficient) _
      (Q'.add_le_self_of_nonneg _ _
        (cutoffTwoOldPulledDiagonal_nonnegative later coefficient))
      (Q'.le_of_eqv
        (Q'.add_comm_eqv
          (cutoffTwoNewDiagonal later coefficient)
          (cutoffTwoOldPulledDiagonal later coefficient)))
  · exact Q'.ge_of_eqv hsplit

private theorem four_term_diagonal_reshuffle
    (oldOld oldNew newOld newNew : Q') :
    (oldOld + oldNew) + (newOld + newNew) ≈
      (oldOld + newNew) + (oldNew + newOld) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv oldOld oldNew (newOld + newNew)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left oldOld _ _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_symm (Q'.add_assoc_eqv oldNew newOld newNew))
        (Q'.add_comm_eqv (oldNew + newOld) newNew))) ?_
  exact Q'.eqv_symm
    (Q'.add_assoc_eqv oldOld newNew (oldNew + newOld))

private theorem diagonal_block_budget_eqv
    (blockRate crossError fullDiagonal oldDiagonal newDiagonal : Q')
    (hsplit : fullDiagonal ≈ oldDiagonal + newDiagonal) :
    (blockRate * oldDiagonal + blockRate * newDiagonal) +
        crossError * fullDiagonal ≈
      cutoffTwoDiagonalBlockRate blockRate crossError * fullDiagonal := by
  unfold cutoffTwoDiagonalBlockRate
  refine Q'.eqv_trans _
    (blockRate * (oldDiagonal + newDiagonal) +
      crossError * fullDiagonal) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.mul_add_eqv blockRate oldDiagonal newDiagonal))
  · refine Q'.eqv_trans _
      (blockRate * fullDiagonal + crossError * fullDiagonal) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left blockRate _ _
          (Q'.eqv_symm hsplit))
    · exact Q'.eqv_symm
        (Q'.add_mul_eqv blockRate crossError fullDiagonal)

/-! ## 2. One full-sector block gap -/

/-- A common contraction on both diagonal blocks plus one cross budget.  The
full-centering hypothesis is retained because applications may use it to
prove the three block estimates. -/
structure CutoffTwoFullSectorDiagonalBlockGapAt
    (later : Nat) (blockRate crossError : Q') : Type 1 where
  later_ge : 2 ≤ later
  old_old_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoOldOldBlock later coefficient) ≤
        blockRate * cutoffTwoOldPulledDiagonal later coefficient
  new_new_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoNewNewBlock later coefficient) ≤
        blockRate * cutoffTwoNewDiagonal later coefficient
  cross_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoOldNewBlock later coefficient) +
          Q'.abs (cutoffTwoNewOldBlock later coefficient) ≤
        crossError * cutoffTwoFullSectorDiagonal later coefficient

namespace CutoffTwoFullSectorDiagonalBlockGapAt

/-- The two diagonal contractions combine at their common rate; only the
cross budget is added. -/
theorem full_abs_gap
    {later : Nat} {blockRate crossError : Q'}
    (certificate : CutoffTwoFullSectorDiagonalBlockGapAt
      later blockRate crossError)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    Q'.abs (cutoffTwoFullSectorMatrix later coefficient) ≤
      cutoffTwoDiagonalBlockRate blockRate crossError *
        cutoffTwoFullSectorDiagonal later coefficient := by
  let oldOld := cutoffTwoOldOldBlock later coefficient
  let oldNew := cutoffTwoOldNewBlock later coefficient
  let newOld := cutoffTwoNewOldBlock later coefficient
  let newNew := cutoffTwoNewNewBlock later coefficient
  let oldDiagonal := cutoffTwoOldPulledDiagonal later coefficient
  let newDiagonal := cutoffTwoNewDiagonal later coefficient
  let fullDiagonal := cutoffTwoFullSectorDiagonal later coefficient
  have hsplit : cutoffTwoFullSectorMatrix later coefficient ≈
      (oldOld + oldNew) + (newOld + newNew) :=
    cutoffTwoFullSectorMatrix_four_blocks later coefficient
  have htriangleOuter :
      Q'.abs ((oldOld + oldNew) + (newOld + newNew)) ≤
        Q'.abs (oldOld + oldNew) + Q'.abs (newOld + newNew) :=
    ExpNeg.abs_add_le _ _
  have htrianglePairs :
      Q'.abs (oldOld + oldNew) + Q'.abs (newOld + newNew) ≤
        (Q'.abs oldOld + Q'.abs oldNew) +
          (Q'.abs newOld + Q'.abs newNew) :=
    Q'.add_le_add (ExpNeg.abs_add_le _ _) (ExpNeg.abs_add_le _ _)
  have hreorder :
      (Q'.abs oldOld + Q'.abs oldNew) +
          (Q'.abs newOld + Q'.abs newNew) ≤
        (Q'.abs oldOld + Q'.abs newNew) +
          (Q'.abs oldNew + Q'.abs newOld) :=
    Q'.le_of_eqv
      (four_term_diagonal_reshuffle
        (Q'.abs oldOld) (Q'.abs oldNew)
        (Q'.abs newOld) (Q'.abs newNew))
  have hblocks :
      (Q'.abs oldOld + Q'.abs newNew) +
          (Q'.abs oldNew + Q'.abs newOld) ≤
        (blockRate * oldDiagonal + blockRate * newDiagonal) +
          crossError * fullDiagonal :=
    Q'.add_le_add
      (Q'.add_le_add
        (certificate.old_old_bound coefficient hcenter)
        (certificate.new_new_bound coefficient hcenter))
      (certificate.cross_bound coefficient hcenter)
  have hdiagonal : fullDiagonal ≈ oldDiagonal + newDiagonal :=
    cutoffTwoFullSectorDiagonal_eqv_oldPulled_add_new
      certificate.later_ge coefficient
  have hbudgetFinal :
      (blockRate * oldDiagonal + blockRate * newDiagonal) +
          crossError * fullDiagonal ≤
        cutoffTwoDiagonalBlockRate blockRate crossError * fullDiagonal :=
    Q'.le_of_eqv
      (diagonal_block_budget_eqv
        blockRate crossError fullDiagonal
        oldDiagonal newDiagonal hdiagonal)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
    (Q'.le_trans' _ _ _ htriangleOuter
      (Q'.le_trans' _ _ _ htrianglePairs
        (Q'.le_trans' _ _ _ hreorder
          (Q'.le_trans' _ _ _ hblocks hbudgetFinal))))

end CutoffTwoFullSectorDiagonalBlockGapAt

/-! ## 3. Cofinal diagonal-block gaps reach completion -/

structure CutoffTwoCofinalFullSectorDiagonalBlockGap
    (blockRate crossError : Q') : Type 1 where
  block_rate_nonnegative : (0 : Q') ≤ blockRate
  cross_error_nonnegative : (0 : Q') ≤ crossError
  full_rate_lt_one :
    cutoffTwoDiagonalBlockRate blockRate crossError < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  gap : ∀ request,
    CutoffTwoFullSectorDiagonalBlockGapAt
      (anchor request) blockRate crossError

namespace CutoffTwoCofinalFullSectorDiagonalBlockGap

def toFiniteStrictGap
    {blockRate crossError : Q'}
    (family : CutoffTwoCofinalFullSectorDiagonalBlockGap
      blockRate crossError) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoDiagonalBlockRate blockRate crossError) where
  rate_nonnegative := by
    unfold cutoffTwoDiagonalBlockRate
    exact Q'.zero_le_add _ _
      family.block_rate_nonnegative family.cross_error_nonnegative
  rate_lt_one := family.full_rate_lt_one
  anchor := family.anchor
  anchor_ge := by
    intro request
    exact Nat.le_trans (Nat.le_max_right 2 request)
      (family.anchor_ge request)
  sectorGap := by
    intro request coefficient hcenter
    exact (family.gap request).full_abs_gap coefficient hcenter

def toCompletedStrictContractionData
    {blockRate crossError : Q'}
    (family : CutoffTwoCofinalFullSectorDiagonalBlockGap
      blockRate crossError) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalFullSectorDiagonalBlockGap

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.cutoffTwoOldPulledDiagonal_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.cutoffTwoNewDiagonal_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.cutoffTwoOldPulledDiagonal_le_full
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.cutoffTwoNewDiagonal_le_full
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.CutoffTwoFullSectorDiagonalBlockGapAt.full_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.CutoffTwoCofinalFullSectorDiagonalBlockGap.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDiagonalBlockGap.CutoffTwoCofinalFullSectorDiagonalBlockGap.toCompletedStrictContractionData
