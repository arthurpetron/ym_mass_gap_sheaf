/-
# The cutoff-two gap in the moving pulled-form language

The canonical cutoff-two finite gap is now stated in the finite forms used by
the cutoff architecture.  The cofinal certificate, however, is phrased using
forms pulled from a later cutoff and a coefficient root-centered against the
later pulled weights.  At `base = later = 2` these pulled entries are exactly
the canonical cutoff-two entries.  This module proves that identity and
inhabits the resulting first nontrivial point of the moving centered-gap
field at rate `49/50`.

This is one finite anchor, not a cofinal family or a persistence theorem.
No thermodynamic or continuum limit, continuum QFT, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumFiniteFormGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private abbrev cutoffTwoStrictRate : Q' :=
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap.cutoffTwoSectorRate49Over50

/-! ## 1. Self-pullback is the canonical finite form -/

theorem cutoffTwoPulledWeight_self_eqv
    {index : Nat}
    (hindex : index ∈
      centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
        (by decide) 2 0) :
    centralPhysicalFinitePulledWeight cutoffTwoHalfCoupling
        (by decide) 2 2 0 index ≈
      centralPhysicalFiniteWeight cutoffTwoHalfCoupling
        (by decide) 2 0 index := by
  have hindexLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hindex
  exact Q'.eqv_of_eq
    (by
      rw [centralPhysicalFinitePulledWeight_eq_rowMarginal
        (Nat.le_refl 2) hindexLt]
      rfl)

theorem cutoffTwoPulledKernel_self_eqv
    {row column : Nat}
    (hrow : row ∈
      centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
        (by decide) 2 0)
    (hcolumn : column ∈
      centralPhysicalFiniteVacuumSectorIndices cutoffTwoHalfCoupling
        (by decide) 2 0) :
    centralPhysicalFinitePulledKernel cutoffTwoHalfCoupling
        (by decide) 2 2 0 row column ≈
      centralPhysicalFiniteKernel cutoffTwoHalfCoupling
        (by decide) 2 0 row column := by
  have hrowLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hrow
  have hcolumnLt := centralPhysicalFiniteVacuumSectorIndex_lt
    cutoffTwoHalfCoupling (by decide) 2 0 hcolumn
  exact Q'.eqv_of_eq
    (by
      rw [centralPhysicalFinitePulledKernel_eq_normalizedKernel
        (Nat.le_refl 2) hrowLt hcolumnLt]
      rfl)

theorem cutoffTwoPulledVacuumSectorWeightedMean_self_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient ≈
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFinitePulledVacuumSectorWeightedMean
    centralPhysicalFiniteVacuumSectorWeightedMean
  apply listQSum_congr_on
  intro index hindex
  exact Q'.mul_eqv_congr_left _ _ _
    (cutoffTwoPulledWeight_self_eqv hindex)

theorem cutoffTwoPulledVacuumSectorDiagonal_self_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient ≈
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  apply listQSum_congr_on
  intro index hindex
  exact Q'.mul_eqv_congr_left _ _ _
    (cutoffTwoPulledWeight_self_eqv hindex)

theorem cutoffTwoPulledVacuumSectorMatrix_self_eqv
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient ≈
      centralPhysicalFiniteVacuumSectorMatrixQuadratic
        cutoffTwoHalfCoupling (by decide) 2 0 coefficient := by
  unfold centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    centralPhysicalFiniteVacuumSectorMatrixQuadratic finiteJointQuadratic
  apply listQSum_congr_on
  intro row hrow
  apply listQSum_congr_on
  intro column hcolumn
  exact Q'.mul_eqv_congr_left _ _ _
    (cutoffTwoPulledKernel_self_eqv hrow hcolumn)

/-! ## 2. The first inhabited moving centered-gap point -/

/-- The exact expression demanded by the cofinal moving centered-gap
certificate is inhabited at the finite anchor `base = later = 2`. -/
theorem cutoffTwoPulledHeadCentered_abs_gap
    (coefficient : Nat → Q') :
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          cutoffTwoHalfCoupling (by decide) 2 2 0
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient)) ≤
      cutoffTwoStrictRate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          cutoffTwoHalfCoupling (by decide) 2 2 0
          (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
            cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient) := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient
  have hpulledCenter :
      centralPhysicalFinitePulledVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) 2 2 0 moving ≈ 0 :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      cutoffTwoHalfCoupling (by decide) 2 2 0 coefficient
  have hcanonicalCenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
          cutoffTwoHalfCoupling (by decide) 2 0 moving ≈ 0 :=
    Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (cutoffTwoPulledVacuumSectorWeightedMean_self_eqv moving))
      hpulledCenter
  have hcanonicalGap := cutoffTwoCanonicalVacuumFinite_abs_gap
    moving hcanonicalCenter
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (cutoffTwoPulledVacuumSectorMatrix_self_eqv moving)))
    (Q'.le_trans' _ _ _ hcanonicalGap
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left cutoffTwoStrictRate _ _
          (Q'.eqv_symm
            (cutoffTwoPulledVacuumSectorDiagonal_self_eqv moving)))))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap.cutoffTwoPulledWeight_self_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap.cutoffTwoPulledKernel_self_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap.cutoffTwoPulledVacuumSectorMatrix_self_eqv
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledVacuumGap.cutoffTwoPulledHeadCentered_abs_gap
