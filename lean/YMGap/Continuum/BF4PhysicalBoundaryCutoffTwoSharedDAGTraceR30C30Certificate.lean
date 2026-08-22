/- Complete compact shared-DAG trace R30C30. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR30C30ExpectedInterface : Q' :=
  (⟨801769362817275, 309485009821345068724781055⟩ : Q')

theorem cutoffTwoSharedDAGTraceR30C30Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR30C30Factors24 ≈
      cutoffTwoSharedDAGTraceR30C30ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR30C30Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR30C30Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR30C30Factors24 :=
  Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR30C30Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR30C30Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR30C30Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR30C30Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR30C30Shard04_partitionSum_eqv (cutoffTwoSharedDAGTraceR30C30Shard05_partitionSum_eqv)))))

theorem cutoffTwoSharedDAGTraceR30C30Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR30C30Factors0 ≈
      cutoffTwoSharedDAGTraceR30C30ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR30C30Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR30C30Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR30C30eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR30C30Factors0 ≈
      cutoffTwoSharedDAGTraceR30C30ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR30C30Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR30C30Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR30C30Certificate.cutoffTwoSharedDAGTraceR30C30eqv_expected
