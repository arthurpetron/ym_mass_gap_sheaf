/- Complete canonical sparse certificate for sector (1, 1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard05

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Certificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard05

local infix:50 " ≈ " => Q'.eqv

theorem canonicalSparseTraceR01C01Terminal_partitionSum_eqv_expected :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        canonicalSparseTraceR01C01Factors24 ≈
      sparseTraceR01C01ExpectedInterface := by
  decide

theorem canonicalSparseTraceR01C01InterfacePartitionSum_ordered_eqv :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        canonicalSparseTraceR01C01Factors0 ≈
      sparseTraceR01C01ExpectedInterface := by
  exact Q'.eqv_trans _ _ _ (Q'.eqv_trans _ _ _ canonicalSparseTraceR01C01Shard00_partitionSum_eqv (Q'.eqv_trans _ _ _ canonicalSparseTraceR01C01Shard01_partitionSum_eqv (Q'.eqv_trans _ _ _ canonicalSparseTraceR01C01Shard02_partitionSum_eqv (Q'.eqv_trans _ _ _ canonicalSparseTraceR01C01Shard03_partitionSum_eqv (Q'.eqv_trans _ _ _ canonicalSparseTraceR01C01Shard04_partitionSum_eqv (canonicalSparseTraceR01C01Shard05_partitionSum_eqv))))))
    canonicalSparseTraceR01C01Terminal_partitionSum_eqv_expected

theorem canonicalSparseTraceR01C01InterfacePartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        canonicalSparseTraceR01C01Factors0 ≈
      sparseTraceR01C01ExpectedInterface := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct canonicalSparseTraceR01C01Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    canonicalSparseTraceR01C01InterfacePartitionSum_ordered_eqv

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Certificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Certificate.canonicalSparseTraceR01C01InterfacePartitionSum_eqv
