/- Compose only the six already checked structural trace segments. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Composition

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Shard05
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSharedDAGTraceR01C01Segments_partitionSum_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR01C01Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR01C01Factors24 := by
  exact Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR01C01Shard00_partitionSum_eqv
    (Q'.eqv_trans _ _ _
      cutoffTwoSharedDAGTraceR01C01Shard01_partitionSum_eqv
      (Q'.eqv_trans _ _ _
        cutoffTwoSharedDAGTraceR01C01Shard02_partitionSum_eqv
        (Q'.eqv_trans _ _ _
          cutoffTwoSharedDAGTraceR01C01Shard03_partitionSum_eqv
          (Q'.eqv_trans _ _ _
            cutoffTwoSharedDAGTraceR01C01Shard04_partitionSum_eqv
            cutoffTwoSharedDAGTraceR01C01Shard05_partitionSum_eqv))))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Composition

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Composition.cutoffTwoSharedDAGTraceR01C01Segments_partitionSum_eqv
