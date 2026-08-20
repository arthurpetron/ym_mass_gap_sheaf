/- Independent cube/cube cross-check for the verified computed recurrence. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernelCubeCrossCheck

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernel
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorCubeTraceStep0
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

/-- The computed recurrence and the audited sparse trace agree on the
cube/cube entry, without reevaluating the large recurrence in the proof. -/
theorem cutoffTwoSectorPairComputedInterface_cube_cube_eqv :
    cutoffTwoSectorPairComputedInterface
        centralLowerCubeState centralLowerCubeState ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  have hcomputed :
      scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
          (cutoffTwoSectorPairInterfaceFactors
            centralLowerCubeState centralLowerCubeState) ≈
        cutoffTwoSectorPairComputedInterface
          centralLowerCubeState centralLowerCubeState :=
    cutoffTwoSectorPairPartitionSum_ordered_eqv_computed
      centralLowerCubeState centralLowerCubeState
  have htrace :
      scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
          (cutoffTwoSectorPairInterfaceFactors
            centralLowerCubeState centralLowerCubeState) ≈
        cutoffTwoCubeExpectedInterfaceSum := by
    simpa only [sectorCubeFactors0] using
      sectorCubeInterfacePartitionSum_ordered_eqv
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hcomputed) htrace

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernelCubeCrossCheck

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorComputedKernelCubeCrossCheck.cutoffTwoSectorPairComputedInterface_cube_cube_eqv
