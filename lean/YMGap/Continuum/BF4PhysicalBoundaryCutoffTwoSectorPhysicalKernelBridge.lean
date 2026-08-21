/-
# The cutoff-two sector table is the restricted physical kernel

This module isolates the representation seam between the exact 65-state table
and the production reflected Yang--Mills kernel.  The generated table's row
sums are checked unconditionally in process-isolated shards.  A single finite
certificate records the still-expensive comparison of all generated entries
with the production kernel; conditional on that certificate, every in-range
table entry and stored weight is identified with the corresponding physical
kernel entry and restricted row sum.

The result is finite-volume and cutoff-two only.  It selects one invariant
sector but supplies no cofinal sector family or continuum limit.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelData
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumRows

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawRowSumRows
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSectorStateAt_mem
    {index : Nat} (hindex : index < 65) :
    cutoffTwoSectorStateAt index ∈ cutoffTwoCubeSectorStates := by
  unfold cutoffTwoSectorStateAt
  have hlength : index < cutoffTwoCubeSectorStates.length := by
    rw [cutoffTwoCubeSectorStates_length]
    exact hindex
  rw [← List.getElem_eq_getD (h := hlength) zeroEdgeLabelling]
  exact List.getElem_mem hlength

/-- The remaining finite representation burden: every generated row agrees
with the exact table.  This structure is deliberately not inhabited here. -/
structure CutoffTwoSectorPhysicalTableCertificate : Type where
  rowsChecked : ∀ row : Nat, row < 65 →
    cutoffTwoSectorRawKernelRowCheck row = true

/-- Conditional on the finite representation certificate, every exact table
entry is the production unnormalized reflected kernel entry on the
corresponding literal sector states. -/
theorem centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw
    (certificate : CutoffTwoSectorPhysicalTableCertificate)
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
        (cutoffTwoSectorStateAt row)
        (cutoffTwoSectorStateAt column) ≈
      cutoffTwoSectorRawKernel row column := by
  have hphysical :=
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_computed
      (cutoffTwoSectorStateAt row) (cutoffTwoSectorStateAt column)
      (cutoffTwoSectorStateAt_mem hrow)
      (cutoffTwoSectorStateAt_mem hcolumn)
  have hcomputed :
      centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
          (cutoffTwoSectorStateAt row)
          (cutoffTwoSectorStateAt column) ≈
        cutoffTwoSectorComputedRawKernel row column := by
    simpa only [cutoffTwoSectorComputedRawKernel] using hphysical
  exact Q'.eqv_trans _ _ _ hcomputed
    (cutoffTwoSectorRawKernelRowCheck_sound
      (certificate.rowsChecked row hrow) hcolumn)

/-! ## 2. The stored weights are exact restricted row sums -/

/-- The stored row weight is therefore the exact sum of production physical
kernel entries over the selected invariant sector. -/
theorem cutoffTwoSectorRawRowSum_eqv_physicalSectorSum
    (certificate : CutoffTwoSectorPhysicalTableCertificate)
    {row : Nat} (hrow : row < 65) :
    listQSum
        (fun column =>
          centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
            (cutoffTwoSectorStateAt row)
            (cutoffTwoSectorStateAt column))
        (List.range 65) ≈
      cutoffTwoSectorRawRowSum row := by
  exact Q'.eqv_trans _ _ _
    (listQSum_congr_on _ _ (List.range 65)
      (fun column hcolumn =>
        centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw
          certificate hrow (List.mem_range.mp hcolumn)))
    (cutoffTwoSectorRawRowSum_eqv_sum hrow)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.cutoffTwoSectorStateAt_mem
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.centralPhysicalReflectedKernel_cutoffTwo_sectorStateAt_eqv_raw
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorPhysicalKernelBridge.cutoffTwoSectorRawRowSum_eqv_physicalSectorSum
