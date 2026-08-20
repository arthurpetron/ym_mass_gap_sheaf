/- Complete compact shared-DAG trace R01C01. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard05

local infix:50 " ≈ " => Q'.eqv

def cutoffTwoSharedDAGTraceR01C01 :
    CheckedReorderedEliminationTrace 2
      cutoffTwoCubeInterfaceEliminationOrder
      cutoffTwoSharedDAGTraceR01C01Factors0
      cutoffTwoSharedDAGTraceR01C01Factors24 :=
  CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge0 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge1 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge2 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge3 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge4 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge5 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge6 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge7 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge8 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge9 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge10 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge11 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge12 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge13 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge14 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge15 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge16 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge17 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge18 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge19 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge20 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge21 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge22 (CheckedReorderedEliminationTrace.step _ _ _ _ _ cutoffTwoSharedDAGTraceR01C01Edge23 (CheckedReorderedEliminationTrace.done cutoffTwoSharedDAGTraceR01C01Factors24))))))))))))))))))))))))

def cutoffTwoSharedDAGTraceR01C01ExpectedInterface : Q' :=
  (1 : Q')

theorem cutoffTwoSharedDAGTraceR01C01Terminal_eqv_expected :
    scopedFactorPartitionSum 2 []
        cutoffTwoSharedDAGTraceR01C01Factors24 ≈
      cutoffTwoSharedDAGTraceR01C01ExpectedInterface := by
  decide

theorem cutoffTwoSharedDAGTraceR01C01Ordered_eqv_expected :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR01C01Factors0 ≈
      cutoffTwoSharedDAGTraceR01C01ExpectedInterface := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR01C01.partitionSum_eqv_terminal
    cutoffTwoSharedDAGTraceR01C01Terminal_eqv_expected

theorem cutoffTwoSharedDAGTraceR01C01eqv_expected :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR01C01Factors0 ≈
      cutoffTwoSharedDAGTraceR01C01ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR01C01Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR01C01Ordered_eqv_expected

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Certificate.cutoffTwoSharedDAGTraceR01C01eqv_expected
