/- Complete compact shared-DAG trace R00C02. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR00C02ExpectedInterface : Q' :=
  (⟨81, 4294967295⟩ : Q')

theorem cutoffTwoSharedDAGTraceR00C02Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C02Factors24 ≈
      cutoffTwoSharedDAGTraceR00C02ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR00C02Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C02Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C02Factors24 :=
  Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C02Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C02Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C02Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C02Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C02Shard04_partitionSum_eqv (cutoffTwoSharedDAGTraceR00C02Shard05_partitionSum_eqv)))))

theorem cutoffTwoSharedDAGTraceR00C02Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C02Factors0 ≈
      cutoffTwoSharedDAGTraceR00C02ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR00C02Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR00C02Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR00C02eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR00C02Factors0 ≈
      cutoffTwoSharedDAGTraceR00C02ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR00C02Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR00C02Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C02Certificate.cutoffTwoSharedDAGTraceR00C02eqv_expected
