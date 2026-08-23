/-
# Full-sector persistence from the cutoff-two signed-form gap

The cutoff-two `49/50` theorem controls the embedded old vacuum component,
but a larger representation cutoff contains genuinely new sector states.  An
arbitrary centered vector on the larger sector must therefore be reduced to a
centered cutoff-two core together with quantitative matrix-tail error and
diagonal inflation.  This module records exactly those two residuals and
proves the resulting full-sector rate

  (49/50) * diagonalFactor + matrixError.

The zero-error, unit-inflation certificate at cutoff two is constructed.  A
constructively cofinal family of the same comparisons compiles to the actual
completed vacuum-sector transfer contraction.  No such unbounded family is
constructed, and no thermodynamic or continuum limit or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge

local infix:50 " ≈ " => Q'.eqv

private abbrev cutoffTwoStrictRate : Q' :=
  cutoffTwoSectorRate49Over50

def cutoffTwoFullSectorRate
    (matrixError diagonalFactor : Q') : Q' :=
  cutoffTwoStrictRate * diagonalFactor + matrixError

def cutoffTwoFullSectorWeightedMean
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorWeightedMean
    cutoffTwoHalfCoupling (by decide) cutoff 0 coefficient

def cutoffTwoFullSectorMatrix
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorMatrixQuadratic
    cutoffTwoHalfCoupling (by decide) cutoff 0 coefficient

def cutoffTwoFullSectorDiagonal
    (cutoff : Nat) (coefficient : Nat → Q') : Q' :=
  centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    cutoffTwoHalfCoupling (by decide) cutoff 0 coefficient

/-! ## 1. One arbitrary later sector -/

/-- Sufficient comparison data from an arbitrary centered later-sector vector
to one centered cutoff-two core vector. -/
structure CutoffTwoFullSectorGapPersistenceAt
    (later : Nat) (matrixError diagonalFactor : Q') : Type 1 where
  later_ge : 2 ≤ later
  recentered : (Nat → Q') → Nat → Q'
  recentered_centered : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      cutoffTwoFullSectorWeightedMean 2 (recentered coefficient) ≈ 0
  matrix_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      Q'.abs (cutoffTwoFullSectorMatrix later coefficient) ≤
        Q'.abs (cutoffTwoFullSectorMatrix 2 (recentered coefficient)) +
          matrixError * cutoffTwoFullSectorDiagonal later coefficient
  diagonal_comparison : ∀ coefficient,
    cutoffTwoFullSectorWeightedMean later coefficient ≈ 0 →
      cutoffTwoFullSectorDiagonal 2 (recentered coefficient) ≤
        diagonalFactor * cutoffTwoFullSectorDiagonal later coefficient

namespace CutoffTwoFullSectorGapPersistenceAt

/-- The exact cutoff-two theorem plus the two residual estimates controls the
entire later vacuum sector. -/
theorem full_abs_gap
    {later : Nat} {matrixError diagonalFactor : Q'}
    (certificate : CutoffTwoFullSectorGapPersistenceAt
      later matrixError diagonalFactor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    Q'.abs (cutoffTwoFullSectorMatrix later coefficient) ≤
      cutoffTwoFullSectorRate matrixError diagonalFactor *
        cutoffTwoFullSectorDiagonal later coefficient := by
  let core := certificate.recentered coefficient
  let coreMatrix := cutoffTwoFullSectorMatrix 2 core
  let coreDiagonal := cutoffTwoFullSectorDiagonal 2 core
  let laterDiagonal := cutoffTwoFullSectorDiagonal later coefficient
  have hcore : Q'.abs coreMatrix ≤
      cutoffTwoStrictRate * coreDiagonal :=
    cutoffTwoCanonicalVacuumFinite_abs_gap core
      (certificate.recentered_centered coefficient hcenter)
  have hscaled :
      cutoffTwoStrictRate * coreDiagonal ≤
        cutoffTwoStrictRate * (diagonalFactor * laterDiagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _
      (certificate.diagonal_comparison coefficient hcenter)
      cutoffTwoSectorRate49Over50_nonnegative
  have hadd :
      Q'.abs coreMatrix + matrixError * laterDiagonal ≤
        cutoffTwoStrictRate * (diagonalFactor * laterDiagonal) +
          matrixError * laterDiagonal :=
    Q'.add_le_add (Q'.le_trans' _ _ _ hcore hscaled)
      (Q'.le_refl' _)
  refine Q'.le_trans' _ _ _
    (certificate.matrix_comparison coefficient hcenter)
    (Q'.le_trans' _ _ _ hadd ?_)
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      ((cutoffTwoStrictRate * diagonalFactor) * laterDiagonal +
        matrixError * laterDiagonal) _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.eqv_symm
          (Q'.mul_assoc_eqv
            cutoffTwoStrictRate diagonalFactor laterDiagonal)))
      (Q'.eqv_symm
        (Q'.add_mul_eqv
          (cutoffTwoStrictRate * diagonalFactor)
          matrixError laterDiagonal)))

end CutoffTwoFullSectorGapPersistenceAt

/-! ## 2. The inhabited finite anchor -/

/-- At cutoff two there is no new-state tail: identity recentering has zero
matrix error and unit diagonal inflation. -/
def cutoffTwoFullSectorGapPersistenceAtAnchor :
    CutoffTwoFullSectorGapPersistenceAt 2 0 1 where
  later_ge := Nat.le_refl 2
  recentered := fun coefficient => coefficient
  recentered_centered := by
    intro _coefficient hcenter
    exact hcenter
  matrix_comparison := by
    intro coefficient _hcenter
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.eqv_trans _
          (Q'.abs (cutoffTwoFullSectorMatrix 2 coefficient) + 0) _
          (Q'.add_eqv_congr_left _ _ _
            (Q'.zero_mul_eqv
              (cutoffTwoFullSectorDiagonal 2 coefficient)))
          (Q'.eqv_of_eq (Q'.add_zero' _))))
  diagonal_comparison := by
    intro coefficient _hcenter
    exact Q'.le_of_eqv
      (Q'.eqv_symm
        (Q'.one_mul_eqv
          (cutoffTwoFullSectorDiagonal 2 coefficient)))

theorem cutoffTwoFullSectorGapPersistenceAtAnchor_abs_gap
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean 2 coefficient ≈ 0) :
    Q'.abs (cutoffTwoFullSectorMatrix 2 coefficient) ≤
      cutoffTwoFullSectorRate 0 1 *
        cutoffTwoFullSectorDiagonal 2 coefficient :=
  cutoffTwoFullSectorGapPersistenceAtAnchor.full_abs_gap
    coefficient hcenter

/-! ## 3. Cofinal persistence reaches the completed transfer -/

/-- One pair of residual budgets and one full-sector comparison on a
constructively cofinal unbounded cutoff schedule. -/
structure CutoffTwoCofinalFullSectorGapPersistence
    (matrixError diagonalFactor : Q') : Type 1 where
  matrix_error_nonnegative : (0 : Q') ≤ matrixError
  diagonal_factor_nonnegative : (0 : Q') ≤ diagonalFactor
  full_rate_lt_one :
    cutoffTwoFullSectorRate matrixError diagonalFactor < (1 : Q')
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  persistence : ∀ request,
    CutoffTwoFullSectorGapPersistenceAt
      (anchor request) matrixError diagonalFactor

namespace CutoffTwoCofinalFullSectorGapPersistence

/-- A cofinal cutoff-two core/tail comparison is precisely a cofinal finite
strict-gap family for the physical vacuum sector. -/
def toFiniteStrictGap
    {matrixError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorGapPersistence
      matrixError diagonalFactor) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoFullSectorRate matrixError diagonalFactor) where
  rate_nonnegative :=
    Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ cutoffTwoSectorRate49Over50_nonnegative
        family.diagonal_factor_nonnegative)
      family.matrix_error_nonnegative
  rate_lt_one := family.full_rate_lt_one
  anchor := family.anchor
  anchor_ge := by
    intro request
    exact Nat.le_trans (Nat.le_max_right 2 request)
      (family.anchor_ge request)
  sectorGap := by
    intro request coefficient hcenter
    exact (family.persistence request).full_abs_gap coefficient hcenter

/-- Consequently the cofinal core/tail comparison gives the actual completed
vacuum-sector transfer contraction. -/
def toCompletedStrictContractionData
    {matrixError diagonalFactor : Q'}
    (family : CutoffTwoCofinalFullSectorGapPersistence
      matrixError diagonalFactor) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalFullSectorGapPersistence

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.CutoffTwoFullSectorGapPersistenceAt.full_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.cutoffTwoFullSectorGapPersistenceAtAnchor
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.cutoffTwoFullSectorGapPersistenceAtAnchor_abs_gap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.CutoffTwoCofinalFullSectorGapPersistence.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence.CutoffTwoCofinalFullSectorGapPersistence.toCompletedStrictContractionData
