/- Complete compact shared-DAG trace R00C01. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR00C01ExpectedInterface : Q' :=
  (1 : Q')

theorem cutoffTwoSharedDAGTraceR00C01Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C01Factors24 ≈
      cutoffTwoSharedDAGTraceR00C01ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR00C01Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C01Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C01Factors24 :=
  Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C01Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C01Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C01Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C01Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C01Shard04_partitionSum_eqv (cutoffTwoSharedDAGTraceR00C01Shard05_partitionSum_eqv)))))

theorem cutoffTwoSharedDAGTraceR00C01Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C01Factors0 ≈
      cutoffTwoSharedDAGTraceR00C01ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR00C01Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR00C01Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR00C01eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR00C01Factors0 ≈
      cutoffTwoSharedDAGTraceR00C01ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR00C01Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR00C01Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C01Certificate.cutoffTwoSharedDAGTraceR00C01eqv_expected
