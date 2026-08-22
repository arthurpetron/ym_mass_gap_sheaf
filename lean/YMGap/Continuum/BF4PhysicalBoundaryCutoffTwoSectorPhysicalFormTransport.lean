/-
# Production-form transport on the cutoff-two sector

The complete shared-DAG table certificate identifies every entry of the
literal 65-state sector with the production reflected Yang--Mills kernel.
This module transports the kernel, row sum, weighted mean, and quadratic
forms to the already certified rational model.

This is finite-volume and cutoff-two only.  No completed-space, uniform,
thermodynamic, continuum, or Clay conclusion is asserted.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
import YMGap.Continuum.FiniteRationalReversibleSpectralCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGRepresentativeCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.FiniteRationalLDLCertificate
open YMGap.Continuum.FiniteRationalReversibleSpectralCertificate
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- The production reflected kernel restricted to the literal 65-state
cutoff-two sector. -/
def cutoffTwoSectorPhysicalKernel (row column : Nat) : Q' :=
  centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
    (cutoffTwoSectorStateAt row) (cutoffTwoSectorStateAt column)

/-- Exact restricted production-kernel row sum on the same sector. -/
def cutoffTwoSectorPhysicalRowSum (row : Nat) : Q' :=
  listQSum (fun column => cutoffTwoSectorPhysicalKernel row column)
    (List.range 65)

theorem cutoffTwoSectorPhysicalKernel_eqv_raw
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65) :
    cutoffTwoSectorPhysicalKernel row column ≈
      cutoffTwoSectorRawKernel row column := by
  change centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorStateAt row) (cutoffTwoSectorStateAt column) ≈
    cutoffTwoSectorRawKernel row column
  exact centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw
    cutoffTwoSectorPhysicalTableCertificateSealed hrow hcolumn

theorem cutoffTwoSectorPhysicalRowSum_eqv_raw
    {row : Nat} (hrow : row < 65) :
    cutoffTwoSectorPhysicalRowSum row ≈
      cutoffTwoSectorRawRowSum row := by
  change listQSum
      (fun column =>
        centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorStateAt row) (cutoffTwoSectorStateAt column))
      (List.range 65) ≈ cutoffTwoSectorRawRowSum row
  exact cutoffTwoSectorRawRowSum_eqv_physicalSectorSum
    cutoffTwoSectorPhysicalTableCertificateSealed hrow

theorem cutoffTwoSectorPhysicalWeightedMean_eqv_raw
    (coefficient : Nat → Q') :
    finiteWeightedMean 65 cutoffTwoSectorPhysicalRowSum coefficient ≈
      finiteWeightedMean 65 cutoffTwoSectorRawRowSum coefficient := by
  unfold finiteWeightedMean
  apply listQSum_congr_on
  intro row hrow
  exact Q'.mul_eqv_congr_left (coefficient row) _ _
    (cutoffTwoSectorPhysicalRowSum_eqv_raw (List.mem_range.mp hrow))

theorem cutoffTwoSectorPhysicalDiagonalQuadratic_eqv_raw
    (coefficient : Nat → Q') :
    finiteDiagonalQuadratic 65 cutoffTwoSectorPhysicalRowSum coefficient ≈
      finiteDiagonalQuadratic 65 cutoffTwoSectorRawRowSum coefficient := by
  unfold finiteDiagonalQuadratic
  apply listQSum_congr_on
  intro row hrow
  exact Q'.mul_eqv_congr_left
    (coefficient row * coefficient row) _ _
    (cutoffTwoSectorPhysicalRowSum_eqv_raw (List.mem_range.mp hrow))

theorem cutoffTwoSectorPhysicalMatrixQuadratic_eqv_raw
    (coefficient : Nat → Q') :
    finiteMatrixQuadratic 65 cutoffTwoSectorPhysicalKernel coefficient ≈
      finiteMatrixQuadratic 65 cutoffTwoSectorRawKernel coefficient := by
  unfold finiteMatrixQuadratic
  apply listQSum_congr_on
  intro row hrow
  apply listQSum_congr_on
  intro column hcolumn
  exact Q'.mul_eqv_congr_left
    (coefficient row * coefficient column) _ _
    (cutoffTwoSectorPhysicalKernel_eqv_raw
      (List.mem_range.mp hrow) (List.mem_range.mp hcolumn))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalUpperGap
