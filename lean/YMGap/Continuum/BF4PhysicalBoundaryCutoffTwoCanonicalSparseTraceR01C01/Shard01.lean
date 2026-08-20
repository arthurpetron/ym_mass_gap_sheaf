/- Generated canonical sparse trace R01C01, shard 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard00

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard01

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard00

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Step4 : CheckedScopedEliminationStep 2
    31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
    canonicalSparseTraceR01C01Factors4 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 4).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors5 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step4.afterFactors

def canonicalSparseTraceR01C01Step5 : CheckedScopedEliminationStep 2
    32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
    canonicalSparseTraceR01C01Factors5 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 5).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors6 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step5.afterFactors

def canonicalSparseTraceR01C01Step6 : CheckedScopedEliminationStep 2
    56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
    canonicalSparseTraceR01C01Factors6 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 6).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors7 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step6.afterFactors

def canonicalSparseTraceR01C01Step7 : CheckedScopedEliminationStep 2
    58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
    canonicalSparseTraceR01C01Factors7 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 7).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors8 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step7.afterFactors

theorem canonicalSparseTraceR01C01Shard01_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        canonicalSparseTraceR01C01Factors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        canonicalSparseTraceR01C01Factors8 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 5)
        canonicalSparseTraceR01C01Factors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step4.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 6)
        canonicalSparseTraceR01C01Factors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step5.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 7)
        canonicalSparseTraceR01C01Factors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step6.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        canonicalSparseTraceR01C01Factors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard01

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard01.canonicalSparseTraceR01C01Shard01_partitionSum_eqv
