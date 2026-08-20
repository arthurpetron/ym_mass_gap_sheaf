/-
# Complete cutoff-two cube interface elimination certificate

This module composes the six independently checked four-step shards, checks
the terminal empty-scope scalar, and transports the result from the proposed
width-five order back to the production fixed-face order.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardF

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate

set_option maxRecDepth 500000
set_option maxHeartbeats 20000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardF
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

theorem terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24) factors24 ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  decide

theorem cutoffTwoCubeInterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoCubeInterfaceFactors ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  exact Q'.eqv_trans _ _ _
    (by simpa only [List.drop_zero, factors0] using
      shardA_partitionSum_eqv)
    (Q'.eqv_trans _ _ _ shardB_partitionSum_eqv
      (Q'.eqv_trans _ _ _ shardC_partitionSum_eqv
        (Q'.eqv_trans _ _ _ shardD_partitionSum_eqv
          (Q'.eqv_trans _ _ _ shardE_partitionSum_eqv
            (Q'.eqv_trans _ _ _ shardF_partitionSum_eqv
              terminal_partitionSum_eqv_expected)))))

theorem cutoffTwoCubeInterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCubeInterfaceFactors ≈
      cutoffTwoCubeExpectedInterfaceSum := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoCubeInterfaceFactors)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoCubeInterfacePartitionSum_ordered_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate.terminal_partitionSum_eqv_expected
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationCertificate.cutoffTwoCubeInterfacePartitionSum_eqv
