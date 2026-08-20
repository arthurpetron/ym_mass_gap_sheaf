/- Balanced composition of cutoff-two elimination shards A through D. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationPrefix

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardC
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem prefixAB_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoVacuumEliminationFaceOrder factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors10 :=
  Q'.eqv_trans _ _ _
    shardA_partitionSum_eqv shardB_partitionSum_eqv

theorem prefixCD_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors10 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 :=
  Q'.eqv_trans _ _ _
    shardC_partitionSum_eqv shardD_partitionSum_eqv

theorem prefix_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoVacuumEliminationFaceOrder factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 :=
  Q'.eqv_trans _ _ _
    prefixAB_partitionSum_eqv prefixCD_partitionSum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationPrefix

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationPrefix.prefix_partitionSum_eqv
