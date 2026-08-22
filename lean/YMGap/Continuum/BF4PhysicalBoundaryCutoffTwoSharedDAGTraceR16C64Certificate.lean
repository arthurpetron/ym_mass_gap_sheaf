/- Complete compact shared-DAG trace R16C64. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR16C64ExpectedInterface : Q' :=
  (⟨801769362817275, 309485009821345068724781055⟩ : Q')

theorem cutoffTwoSharedDAGTraceR16C64Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR16C64Factors24 ≈
      cutoffTwoSharedDAGTraceR16C64ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR16C64Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR16C64Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR16C64Factors24 :=
  Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR16C64Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR16C64Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR16C64Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR16C64Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR16C64Shard04_partitionSum_eqv (cutoffTwoSharedDAGTraceR16C64Shard05_partitionSum_eqv)))))

theorem cutoffTwoSharedDAGTraceR16C64Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR16C64Factors0 ≈
      cutoffTwoSharedDAGTraceR16C64ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR16C64Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR16C64Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR16C64eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR16C64Factors0 ≈
      cutoffTwoSharedDAGTraceR16C64ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR16C64Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR16C64Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR16C64Certificate.cutoffTwoSharedDAGTraceR16C64eqv_expected
