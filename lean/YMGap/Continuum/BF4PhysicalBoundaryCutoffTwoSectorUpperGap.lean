/-
# Exact canonical upper gap on the cutoff-two 65-state sector

The historical `64 x 64` cleared LDL table is compared entry by entry with
the canonical positive-head pullback of `(49/50) D - K + d d^T`.  The 4096
comparisons are kernel checked in separate row modules.  Their composition
turns that table into an upper-only centered restriction certificate and
therefore proves `K <= (49/50) D` for every exactly centered coefficient on
the verified 65-state sector.

This is a strict finite-sector non-vacuity witness for the arbitrary-rate
upper-only compiler.  It is not a certificate on the full physical carrier,
not a cofinal cutoff family, not a completed-space modulus, and not a
thermodynamic, continuum, or Clay mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGapRows
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate
import YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLDLCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalCutoffCofinalStrictGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalCenteredRestrictionCertificate
open YMGap.Continuum.FiniteRationalHeadCenteredCoordinates
open YMGap.Continuum.FiniteRationalHeadCenteredPullback
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The historical table is the canonical upper pullback -/

/-- Every historical table entry agrees with its sparse canonical formula. -/
theorem cutoffTwoSectorMeanZeroMatrix_eqv_sparseAt49Over50
    {row column : Nat} (hrow : row < 64) (hcolumn : column < 64) :
    cutoffTwoSectorMeanZeroMatrix row column ≈
      cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50 row column := by
  have hrowCheck := List.all_eq_true.mp
    cutoffTwoSectorCanonicalUpperBridgeRows_checked row
    (List.mem_range.mpr hrow)
  unfold cutoffTwoSectorCanonicalUpperBridgeRowCheck at hrowCheck
  have hentry := List.all_eq_true.mp hrowCheck column
    (List.mem_range.mpr hcolumn)
  exact of_decide_eq_true hentry

/-- Every historical table entry is the corresponding canonical upper
positive-head entry at rate `49/50`. -/
theorem cutoffTwoSectorMeanZeroMatrix_eqv_canonicalUpperAt49Over50
    {row column : Nat} (hrow : row < 64) (hcolumn : column < 64) :
    cutoffTwoSectorMeanZeroMatrix row column ≈
      finiteHeadCenteredUpperMatrix
        64 cutoffTwoSectorRate49Over50
        cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
        cutoffTwoSectorRawRowSum_zero_pos_at49Over50 row column :=
  Q'.eqv_trans _
    (cutoffTwoSectorCanonicalUpperSparseEntryAt49Over50 row column) _
    (cutoffTwoSectorMeanZeroMatrix_eqv_sparseAt49Over50 hrow hcolumn)
    (Q'.eqv_symm
      (cutoffTwoSectorCanonicalUpper_eqv_sparseAt49Over50
        row column hrow hcolumn))

private theorem finiteMatrixQuadratic_matrix_congr
    {n : Nat} {left right : Nat → Nat → Q'}
    (hagrees :
      ∀ i, i < n → ∀ j, j < n → left i j ≈ right i j)
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic n left coefficient ≈
      finiteMatrixQuadratic n right coefficient := by
  unfold finiteMatrixQuadratic
  apply listQSum_congr_on
  intro i hi
  apply listQSum_congr_on
  intro j hj
  exact Q'.mul_eqv_congr_left
    (coefficient i * coefficient j) _ _
    (hagrees i (List.mem_range.mp hi) j (List.mem_range.mp hj))

/-! ## 2. Package the historical cleared LDL table -/

/-- The canonical positive-head restriction with the historical matrix used
as its definitionally visible upper matrix. -/
def cutoffTwoSectorUpperRestrictionAt49Over50 :
    FiniteCenteredTwoSidedRestriction
      65 cutoffTwoSectorRate49Over50
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel :=
  finiteHeadCenteredTwoSidedRestriction
    64 cutoffTwoSectorRate49Over50
    cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
    cutoffTwoSectorRawRowSum_zero_pos_at49Over50
    cutoffTwoSectorMeanZeroMatrix
    (finiteHeadCenteredLowerMatrix
      64 cutoffTwoSectorRate49Over50
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
      cutoffTwoSectorRawRowSum_zero_pos_at49Over50)
    (fun coefficient =>
      Q'.eqv_trans _
        (finiteMatrixQuadratic 64
          (finiteHeadCenteredUpperMatrix
            64 cutoffTwoSectorRate49Over50
            cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
            cutoffTwoSectorRawRowSum_zero_pos_at49Over50)
          coefficient) _
        (finiteMatrixQuadratic_matrix_congr
          (fun i hi j hj =>
            cutoffTwoSectorMeanZeroMatrix_eqv_canonicalUpperAt49Over50
              (row := i) (column := j) hi hj)
          coefficient)
        (finiteHeadCenteredUpperMatrix_identify
          64 cutoffTwoSectorRate49Over50
          cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
          cutoffTwoSectorRawRowSum_zero_pos_at49Over50 coefficient))
    (finiteHeadCenteredLowerMatrix_identify
      64 cutoffTwoSectorRate49Over50
      cutoffTwoSectorRawRowSum cutoffTwoSectorRawKernel
      cutoffTwoSectorRawRowSum_zero_pos_at49Over50)

/-- The historical cleared LDL table, now pinned to the canonical upper
restriction instead of merely certifying an unnamed positive matrix. -/
def cutoffTwoSectorUpperClearedLDLCertificateAt49Over50 :
    FiniteCenteredRestrictionUpperClearedLDLCertificate
      cutoffTwoSectorUpperRestrictionAt49Over50 where
  upperLower := cutoffTwoSectorLower
  upperDiagonal := cutoffTwoSectorDiagonal
  upperCommon := cutoffTwoSectorCommonDenominator
  upperRowsCheck := cutoffTwoSectorLDLRows_checked
  upperTriangular := cutoffTwoSectorLower_upper_zero
  upperDiagonalCheck := cutoffTwoSectorLDLDiagonal_checked

/-! ## 3. Contract the certificate to the finite-sector inequality -/

/-- Exact strict upper contraction on every centered coefficient of the
verified cutoff-two 65-state sector. -/
theorem cutoffTwoSectorMeanZeroUpperGapAt49Over50
    (coefficient : Nat → Q')
    (hcenter :
      finiteWeightedMean 65 cutoffTwoSectorRawRowSum coefficient ≈ 0) :
    finiteMatrixQuadratic 65 cutoffTwoSectorRawKernel coefficient ≤
      cutoffTwoSectorRate49Over50 *
        finiteDiagonalQuadratic 65
          cutoffTwoSectorRawRowSum coefficient :=
  cutoffTwoSectorUpperClearedLDLCertificateAt49Over50.upperContraction
    coefficient hcenter

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorMeanZeroMatrix_eqv_canonicalUpperAt49Over50
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorMeanZeroUpperGapAt49Over50
