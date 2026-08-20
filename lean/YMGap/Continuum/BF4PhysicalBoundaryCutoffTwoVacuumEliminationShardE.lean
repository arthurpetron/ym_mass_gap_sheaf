/- Balanced composition of cutoff-two elimination steps 14 through 18. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardE

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem shardE_first_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 16) factors16 :=
  Q'.eqv_trans _ _ _
    step14_partitionSum_eqv step15_partitionSum_eqv

theorem shardE_second_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 16) factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 :=
  Q'.eqv_trans _ _ _ step16_partitionSum_eqv
    (Q'.eqv_trans _ _ _
      step17_partitionSum_eqv step18_partitionSum_eqv)

theorem shardE_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 :=
  Q'.eqv_trans _ _ _
    shardE_first_partitionSum_eqv shardE_second_partitionSum_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardE

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardE.shardE_partitionSum_eqv
