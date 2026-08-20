/- Complete compact shared-DAG trace R00C00. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR00C00ExpectedInterface : Q' :=
  (⟨79228171482694884378979459057, 79228162514264337593543950335⟩ : Q')

theorem cutoffTwoSharedDAGTraceR00C00Terminal_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C00Factors24 ≈
      cutoffTwoSharedDAGTraceR00C00ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR00C00Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C00Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR00C00Factors24 :=
  Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C00Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C00Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C00Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C00Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ cutoffTwoSharedDAGTraceR00C00Shard04_partitionSum_eqv (cutoffTwoSharedDAGTraceR00C00Shard05_partitionSum_eqv)))))

theorem cutoffTwoSharedDAGTraceR00C00Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR00C00Factors0 ≈
      cutoffTwoSharedDAGTraceR00C00ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR00C00Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR00C00Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR00C00eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR00C00Factors0 ≈
      cutoffTwoSharedDAGTraceR00C00ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR00C00Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR00C00Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR00C00Certificate.cutoffTwoSharedDAGTraceR00C00eqv_expected
