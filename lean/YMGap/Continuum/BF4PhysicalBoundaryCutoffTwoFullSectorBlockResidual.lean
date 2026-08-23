/-
# Old/new block residual compiler for full-sector persistence

The exact later-sector quadratic is the sum of old-old, old-new, new-old,
and new-new blocks relative to the embedded cutoff-two component.  This
module expands the matrix comparison required by full-sector persistence into
four separately bounded residuals.  Their errors add, while the diagonal
inflation remains a single comparison for the recentered cutoff-two core.

A constructively cofinal family of these block estimates contracts through
the cutoff-two `49/50` theorem to the actual completed vacuum-sector transfer
contraction.  No later-cutoff block estimate or cofinal family is constructed
here, and no thermodynamic or continuum limit or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.FiniteDeterministicKernelPushforward

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoOldOldBlock
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoOldNewBlock
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointBlock
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoNewOldBlock
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorOldBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoNewNewBlock
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointBlock
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    (centralPhysicalFiniteVacuumSectorNewBlockIndices
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient
    (centralPhysicalFiniteKernel
      cutoffTwoHalfCoupling (by decide) later 0)

def cutoffTwoBlockMatrixError
    (oldOldError oldNewError newOldError newNewError : Q') : Q' :=
  (oldOldError + oldNewError) + (newOldError + newNewError)

/-- The generic old/new decomposition specialized once to the cutoff-two
base.  Naming the specialization prevents later proofs from repeatedly
unfolding the full physical-kernel definitions during unification. -/
theorem cutoffTwoFullSectorMatrix_four_blocks
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorMatrix later coefficient ≈
      (cutoffTwoOldOldBlock later coefficient +
          cutoffTwoOldNewBlock later coefficient) +
        (cutoffTwoNewOldBlock later coefficient +
          cutoffTwoNewNewBlock later coefficient) := by
  unfold cutoffTwoFullSectorMatrix cutoffTwoOldOldBlock
    cutoffTwoOldNewBlock cutoffTwoNewOldBlock cutoffTwoNewNewBlock
  exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_four_blocks
    cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient

private theorem four_error_terms_eqv
    (base oldOldError oldNewError newOldError newNewError diagonal : Q') :
    ((base + oldOldError * diagonal) + oldNewError * diagonal) +
        (newOldError * diagonal + newNewError * diagonal) ≈
      base +
        cutoffTwoBlockMatrixError
          oldOldError oldNewError newOldError newNewError * diagonal := by
  unfold cutoffTwoBlockMatrixError
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_assoc_eqv base
        (oldOldError * diagonal) (oldNewError * diagonal))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv base
      (oldOldError * diagonal + oldNewError * diagonal)
      (newOldError * diagonal + newNewError * diagonal)) ?_
  refine Q'.add_eqv_congr_left base _ _ ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.eqv_symm (Q'.add_mul_eqv oldOldError oldNewError diagonal))
      (Q'.eqv_symm (Q'.add_mul_eqv newOldError newNewError diagonal))) ?_
  exact Q'.eqv_symm
    (Q'.add_mul_eqv
      (oldOldError + oldNewError) (newOldError + newNewError) diagonal)

/-! ## 1. One later cutoff, split into four residual blocks -/

/-- Separately checkable old/new block data sufficient for the aggregate
full-sector comparison. -/
structure CutoffTwoFullSectorBlockResidualAt
    (later : Nat)
    (oldOldError oldNewError newOldError newNewError diagonalFactor : Q') :
    Type 1 where
  later_ge : 2 ≤ later
  recentered : (Nat → Q') → Nat → Q'
  recentered_centered : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      cutoffTwoFullSectorWeightedMean 2 (recentered coefficient) ≈ 0
  old_old_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoOldOldBlock later coefficient) ≤
        Q'.abs
            (cutoffTwoFullSectorMatrix 2 (recentered coefficient)) +
          oldOldError * cutoffTwoFullSectorDiagonal later coefficient
  old_new_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoOldNewBlock later coefficient) ≤
        oldNewError * cutoffTwoFullSectorDiagonal later coefficient
  new_old_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoNewOldBlock later coefficient) ≤
        newOldError * cutoffTwoFullSectorDiagonal later coefficient
  new_new_bound : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoNewNewBlock later coefficient) ≤
        newNewError * cutoffTwoFullSectorDiagonal later coefficient
  diagonal_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      cutoffTwoFullSectorDiagonal 2 (recentered coefficient) ≤
        diagonalFactor * cutoffTwoFullSectorDiagonal later coefficient

namespace CutoffTwoFullSectorBlockResidualAt

/-- The four block residuals add to the aggregate matrix-tail error required
by `CutoffTwoFullSectorGapPersistenceAt`. -/
def toFullSectorGapPersistenceAt
    {later : Nat}
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (residual : CutoffTwoFullSectorBlockResidualAt later
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CutoffTwoFullSectorGapPersistenceAt later
      (cutoffTwoBlockMatrixError
        oldOldError oldNewError newOldError newNewError)
      diagonalFactor where
  later_ge := residual.later_ge
  recentered := residual.recentered
  recentered_centered := residual.recentered_centered
  diagonal_comparison := residual.diagonal_comparison
  matrix_comparison := by
    intro coefficient hcenter
    let oldOld := cutoffTwoOldOldBlock later coefficient
    let oldNew := cutoffTwoOldNewBlock later coefficient
    let newOld := cutoffTwoNewOldBlock later coefficient
    let newNew := cutoffTwoNewNewBlock later coefficient
    let coreMatrix :=
      cutoffTwoFullSectorMatrix 2 (residual.recentered coefficient)
    let diagonal := cutoffTwoFullSectorDiagonal later coefficient
    have hsplit : cutoffTwoFullSectorMatrix later coefficient ≈
        (oldOld + oldNew) + (newOld + newNew) := by
      exact cutoffTwoFullSectorMatrix_four_blocks later coefficient
    have htriangleOuter :
        Q'.abs ((oldOld + oldNew) + (newOld + newNew)) ≤
          Q'.abs (oldOld + oldNew) + Q'.abs (newOld + newNew) :=
      ExpNeg.abs_add_le _ _
    have htrianglePairs :
        Q'.abs (oldOld + oldNew) + Q'.abs (newOld + newNew) ≤
          (Q'.abs oldOld + Q'.abs oldNew) +
            (Q'.abs newOld + Q'.abs newNew) :=
      Q'.add_le_add (ExpNeg.abs_add_le _ _) (ExpNeg.abs_add_le _ _)
    have hblocks :
        (Q'.abs oldOld + Q'.abs oldNew) +
            (Q'.abs newOld + Q'.abs newNew) ≤
          ((Q'.abs coreMatrix + oldOldError * diagonal) +
              oldNewError * diagonal) +
            (newOldError * diagonal + newNewError * diagonal) :=
      Q'.add_le_add
        (Q'.add_le_add
          (residual.old_old_comparison coefficient hcenter)
          (residual.old_new_bound coefficient hcenter))
        (Q'.add_le_add
          (residual.new_old_bound coefficient hcenter)
          (residual.new_new_bound coefficient hcenter))
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hsplit))
      (Q'.le_trans' _ _ _ htriangleOuter
        (Q'.le_trans' _ _ _ htrianglePairs
          (Q'.le_trans' _ _ _ hblocks
            (Q'.le_of_eqv
              (four_error_terms_eqv
                (Q'.abs coreMatrix) oldOldError oldNewError
                newOldError newNewError diagonal)))))

end CutoffTwoFullSectorBlockResidualAt

/-! ## 2. Cofinal block control -/

/-- Uniform nonnegative block budgets on a constructively cofinal unbounded
schedule, with the exact composed strict-rate condition. -/
structure CutoffTwoCofinalFullSectorBlockResidual
    (oldOldError oldNewError newOldError newNewError diagonalFactor : Q') :
    Type 1 where
  old_old_error_nonnegative : (0 : Q') ≤ oldOldError
  old_new_error_nonnegative : (0 : Q') ≤ oldNewError
  new_old_error_nonnegative : (0 : Q') ≤ newOldError
  new_new_error_nonnegative : (0 : Q') ≤ newNewError
  diagonal_factor_nonnegative : (0 : Q') ≤ diagonalFactor
  full_rate_lt_one :
    cutoffTwoFullSectorRate
        (cutoffTwoBlockMatrixError
          oldOldError oldNewError newOldError newNewError)
        diagonalFactor < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  residual : ∀ request,
    CutoffTwoFullSectorBlockResidualAt (anchor request)
      oldOldError oldNewError newOldError newNewError diagonalFactor

namespace CutoffTwoCofinalFullSectorBlockResidual

def matrixError_nonnegative
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorBlockResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    (0 : Q') ≤ cutoffTwoBlockMatrixError
      oldOldError oldNewError newOldError newNewError := by
  unfold cutoffTwoBlockMatrixError
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _ family.old_old_error_nonnegative
      family.old_new_error_nonnegative)
    (Q'.zero_le_add _ _ family.new_old_error_nonnegative
      family.new_new_error_nonnegative)

def toCofinalFullSectorGapPersistence
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorBlockResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CutoffTwoCofinalFullSectorGapPersistence
      (cutoffTwoBlockMatrixError
        oldOldError oldNewError newOldError newNewError)
      diagonalFactor where
  matrix_error_nonnegative := family.matrixError_nonnegative
  diagonal_factor_nonnegative := family.diagonal_factor_nonnegative
  full_rate_lt_one := family.full_rate_lt_one
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  persistence := by
    intro request
    exact (family.residual request).toFullSectorGapPersistenceAt

def toCompletedStrictContractionData
    {oldOldError oldNewError newOldError newNewError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorBlockResidual
      oldOldError oldNewError newOldError newNewError diagonalFactor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalFullSectorGapPersistence.toCompletedStrictContractionData

end CutoffTwoCofinalFullSectorBlockResidual

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual.CutoffTwoFullSectorBlockResidualAt.toFullSectorGapPersistenceAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual.CutoffTwoCofinalFullSectorBlockResidual.matrixError_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual.CutoffTwoCofinalFullSectorBlockResidual.toCofinalFullSectorGapPersistence
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorBlockResidual.CutoffTwoCofinalFullSectorBlockResidual.toCompletedStrictContractionData
