/-
# Cutoff-two vacuum-column elimination, shard C

Composition of the independently chunk-checked high-width steps ten through
twelve.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardC

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem shardC_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors10 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 13) factors13 := by
  exact Q'.eqv_trans _ _ _ step10_partitionSum_eqv
    (Q'.eqv_trans _ _ _ step11_partitionSum_eqv
      step12_partitionSum_eqv)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardC

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardC.shardC_partitionSum_eqv

