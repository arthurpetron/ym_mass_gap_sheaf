/- Balanced composition of the final cutoff-two elimination steps. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardF

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTerminal
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem shardF_first_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 21) factors21 :=
  Q'.eqv_trans _ _ _
    step19_partitionSum_eqv step20_partitionSum_eqv

theorem shardF_second_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 21) factors21 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 24) factors24 :=
  Q'.eqv_trans _ _ _ step21_partitionSum_eqv
    (Q'.eqv_trans _ _ _
      step22_partitionSum_eqv step23_partitionSum_eqv)

theorem shardF_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 24) factors24 :=
  Q'.eqv_trans _ _ _
    shardF_first_partitionSum_eqv shardF_second_partitionSum_eqv

theorem shardF_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 ≈
      cutoffTwoVacuumExpectedScalar :=
  Q'.eqv_trans _ _ _
    shardF_partitionSum_eqv terminal_partitionSum_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardF

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardF.shardF_partitionSum_eqv_expected
