/-
# The finite Poincare gap on the actual cutoff-two pulled moving forms

At every representation cutoff at least two, extend the cutoff-two moving
head-centered coefficient by zero to the full finite vacuum sector.  The
extension is exactly centered, and its full matrix and diagonal forms are
exactly the pulled cutoff-two forms.  The explicit finite-sector Poincare
theorem therefore gives a strict form rate for the literal approximants of
the cutoff-two moving Bishop reals.

The resulting rate is independent of the coefficient at each fixed cutoff,
but still depends on that cutoff.  This module does not claim a cutoff-uniform
rate, a thermodynamic limit, a continuum QFT, or the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledTailSeedGapBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredDiagonalCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCenteredMatrixCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The cutoff-dependent strict rate -/

/-- The canonical Poincare rate of the full finite vacuum sector at the
current representation cutoff. -/
def cutoffTwoPulledPoincareRateAt (cutoff : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorPoincareRate
    cutoffTwoHalfCoupling (by decide) cutoff 0

theorem cutoffTwoPulledPoincareRateAt_nonnegative (cutoff : Nat) :
    (0 : Q') ≤ cutoffTwoPulledPoincareRateAt cutoff := by
  exact centralPhysicalFiniteVacuumSectorPoincareRate_nonnegative
    cutoffTwoHalfCoupling (by decide) cutoff 0

theorem cutoffTwoPulledPoincareRateAt_lt_one (cutoff : Nat) :
    cutoffTwoPulledPoincareRateAt cutoff < (1 : Q') := by
  exact centralPhysicalFiniteVacuumSectorPoincareRate_lt_one
    cutoffTwoHalfCoupling (by decide) cutoff 0

/-! ## 2. Named exact recoding seams -/

/-- The compact moving-matrix approximant is exactly the displayed pulled
physical quadratic. -/
theorem cutoffTwoActualMovingMatrixAt_eqv_pulled
    (cutoff : Nat) (coefficient : Nat → Q') :
    cutoffTwoActualMovingMatrixAt cutoff coefficient ≈
      cutoffTwoPulledMatrixAt cutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient) := by
  apply Q'.eqv_of_eq
  unfold cutoffTwoActualMovingMatrixAt cutoffTwoPulledMovingMatrix
    cutoffTwoMovingMatrixLimit
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx]
  rfl

/-- The compact moving-diagonal approximant is exactly the displayed pulled
physical diagonal quadratic. -/
theorem cutoffTwoActualMovingDiagonalAt_eqv_pulled
    (cutoff : Nat) (coefficient : Nat → Q') :
    cutoffTwoActualMovingDiagonalAt cutoff coefficient ≈
      cutoffTwoPulledDiagonalAt cutoff
        (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient) := by
  apply Q'.eqv_of_eq
  unfold cutoffTwoActualMovingDiagonalAt cutoffTwoPulledMovingDiagonal
    cutoffTwoMovingDiagonalLimit
  rw [centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx]
  rfl

/-- The actual moving diagonal is nonnegative at every cutoff. -/
theorem cutoffTwoActualMovingDiagonalAt_nonnegative
    (cutoff : Nat) (coefficient : Nat → Q') :
    (0 : Q') ≤ cutoffTwoActualMovingDiagonalAt cutoff coefficient := by
  exact Q'.le_trans' _ _ _
    (cutoffTwoPulledDiagonalAt_nonnegative cutoff
      (cutoffTwoPulledMovingCenteredCoefficientAt cutoff coefficient))
    (Q'.ge_of_eqv
      (cutoffTwoActualMovingDiagonalAt_eqv_pulled cutoff coefficient))

/-! ## 3. Exact transport to the moving pulled forms -/

/-- At every cutoff at least two, the literal cutoff-two moving approximants
obey the strict full-sector Poincare rate at that cutoff.  No persistence
certificate or asymptotic hypothesis is needed for this finite statement. -/
theorem cutoffTwoActualMoving_abs_gap_at_poincareRate
    (cutoff : Nat) (hcutoff : 2 ≤ cutoff)
    (coefficient : Nat → Q') :
    Q'.abs (cutoffTwoActualMovingMatrixAt cutoff coefficient) ≤
      cutoffTwoPulledPoincareRateAt cutoff *
        cutoffTwoActualMovingDiagonalAt cutoff coefficient := by
  let moving : Nat → Q' :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      cutoffTwoHalfCoupling (by decide) 2 cutoff 0 coefficient
  let extended : Nat → Q' :=
    centralPhysicalFiniteVacuumSectorCoefficientExtension
      cutoffTwoHalfCoupling (by decide) 2 cutoff 0 moving
  have hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) cutoff 0 extended ≈ 0 :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtension_meanZero
      hcutoff coefficient
  have hfinite :
      Q'.abs
          (centralPhysicalFiniteVacuumSectorMatrixQuadratic
            cutoffTwoHalfCoupling (by decide) cutoff 0 extended) ≤
        cutoffTwoPulledPoincareRateAt cutoff *
          centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            cutoffTwoHalfCoupling (by decide) cutoff 0 extended := by
    exact centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal
      cutoffTwoHalfCoupling (by decide) cutoff 0 extended hcenter
  have hmatrix :
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) cutoff 0 extended ≈
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) 2 cutoff 0 moving :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      hcutoff coefficient
  have hdiagonal :
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) cutoff 0 extended ≈
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 cutoff 0 moving :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
      hcutoff coefficient
  have hactualMatrix :
      cutoffTwoActualMovingMatrixAt cutoff coefficient ≈
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) 2 cutoff 0 moving := by
    apply Q'.eqv_of_eq
    unfold cutoffTwoActualMovingMatrixAt cutoffTwoPulledMovingMatrix
      cutoffTwoMovingMatrixLimit
    exact
      centralPhysicalFinitePulledVacuumSectorHeadCenteredMatrixCutoffLimit_approx
        (by decide) (by decide) 2 0 coefficient cutoff
  have hactualDiagonal :
      cutoffTwoActualMovingDiagonalAt cutoff coefficient ≈
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 cutoff 0 moving := by
    apply Q'.eqv_of_eq
    unfold cutoffTwoActualMovingDiagonalAt cutoffTwoPulledMovingDiagonal
      cutoffTwoMovingDiagonalLimit
    exact
      centralPhysicalFinitePulledVacuumSectorHeadCenteredDiagonalCutoffLimit_approx
        (by decide) (by decide) 2 0 coefficient cutoff
  have hmatrixToFull :
      cutoffTwoActualMovingMatrixAt cutoff coefficient ≈
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) cutoff 0 extended :=
    Q'.eqv_trans _ _ _ hactualMatrix (Q'.eqv_symm hmatrix)
  have hfullDiagonalToActual :
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) cutoff 0 extended ≈
        cutoffTwoActualMovingDiagonalAt cutoff coefficient :=
    Q'.eqv_trans _ _ _ hdiagonal (Q'.eqv_symm hactualDiagonal)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hmatrixToFull))
    (Q'.le_trans' _ _ _ hfinite
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          (cutoffTwoPulledPoincareRateAt cutoff) _ _
          hfullDiagonalToActual)))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoPulledPoincareRateAt_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoPulledPoincareRateAt_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoActualMovingMatrixAt_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoActualMovingDiagonalAt_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoActualMovingDiagonalAt_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledPoincareGap.cutoffTwoActualMoving_abs_gap_at_poincareRate
