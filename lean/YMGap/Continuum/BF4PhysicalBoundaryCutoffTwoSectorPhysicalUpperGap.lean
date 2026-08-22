/-
# Unconditional production-kernel upper gap on the cutoff-two sector

The complete shared-DAG table certificate identifies every entry of the
literal 65-state sector with the production reflected Yang--Mills kernel.
Transporting the already checked rational `49/50` upper-gap certificate across
that identification gives a statement written entirely with the production
kernel and its exact restricted row sums.

This is finite-volume and cutoff-two only.  It is not a cofinal cutoff family,
a completed-space estimate, a thermodynamic or continuum limit, or a Clay
mass-gap theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalGramPositivity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorUpperGap
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

local infix:50 " ≈ " => Q'.eqv

/-! ## Strict centered contraction -/

/-- Exact strict upper contraction of the production reflected kernel on every
coefficient centered with respect to its own restricted physical row sums. -/
theorem cutoffTwoSectorPhysicalMeanZeroUpperGapAt49Over50
    (coefficient : Nat → Q')
    (hcenter :
      finiteWeightedMean 65 cutoffTwoSectorPhysicalRowSum coefficient ≈ 0) :
    finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient ≤
      cutoffTwoSectorRate49Over50 *
        finiteDiagonalQuadratic 65
          cutoffTwoSectorPhysicalRowSum coefficient := by
  have hmean := cutoffTwoSectorPhysicalWeightedMean_eqv_raw coefficient
  have hcenterRaw :
      finiteWeightedMean 65 cutoffTwoSectorRawRowSum coefficient ≈ 0 :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hmean) hcenter
  have hraw := cutoffTwoSectorMeanZeroUpperGapAt49Over50
    coefficient hcenterRaw
  have hkernel := cutoffTwoSectorPhysicalMatrixQuadratic_eqv_raw coefficient
  have hdiagonal :=
    cutoffTwoSectorPhysicalDiagonalQuadratic_eqv_raw coefficient
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hkernel)
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left cutoffTwoSectorRate49Over50 _ _
          (Q'.eqv_symm hdiagonal))))

/-- Because the production kernel is a Gram kernel, its upper contraction is
already an absolute centered contraction; no separate lower LDL table is
needed at this finite sector. -/
theorem cutoffTwoSectorPhysicalMeanZeroAbsGapAt49Over50
    (coefficient : Nat → Q')
    (hcenter :
      finiteWeightedMean 65 cutoffTwoSectorPhysicalRowSum coefficient ≈ 0) :
    Q'.abs
        (finiteMatrixQuadratic 65
          cutoffTwoSectorPhysicalKernel coefficient) ≤
      cutoffTwoSectorRate49Over50 *
        finiteDiagonalQuadratic 65
          cutoffTwoSectorPhysicalRowSum coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (cutoffTwoSectorPhysicalMatrixQuadratic_nonnegative coefficient)]
  exact cutoffTwoSectorPhysicalMeanZeroUpperGapAt49Over50
    coefficient hcenter

/-- The finite production-sector estimate carries an explicit strict rate. -/
theorem cutoffTwoSectorPhysicalStrictAbsGapAt49Over50 :
    cutoffTwoSectorRate49Over50 < (1 : Q') ∧
      ∀ coefficient : Nat → Q',
        finiteWeightedMean 65
            cutoffTwoSectorPhysicalRowSum coefficient ≈ 0 →
          Q'.abs
              (finiteMatrixQuadratic 65
                cutoffTwoSectorPhysicalKernel coefficient) ≤
            cutoffTwoSectorRate49Over50 *
              finiteDiagonalQuadratic 65
                cutoffTwoSectorPhysicalRowSum coefficient := by
  exact ⟨cutoffTwoSectorRate49Over50_lt_one,
    cutoffTwoSectorPhysicalMeanZeroAbsGapAt49Over50⟩

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
