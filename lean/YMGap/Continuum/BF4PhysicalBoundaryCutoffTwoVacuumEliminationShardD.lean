/-
# Cutoff-two vacuum-column elimination, shard D

The single maximum-width elimination step, certified by independently compiled
finite chunks.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem shardD_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 13) factors13 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 :=
  step13_partitionSum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardD.shardD_partitionSum_eqv
