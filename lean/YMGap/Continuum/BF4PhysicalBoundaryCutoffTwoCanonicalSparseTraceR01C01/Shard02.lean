/- Generated canonical sparse trace R01C01, shard 2. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard01

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard02

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard01

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Step8 : CheckedScopedEliminationStep 2
    23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
    canonicalSparseTraceR01C01Factors8 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 8).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors9 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step8.afterFactors

def canonicalSparseTraceR01C01Step9 : CheckedScopedEliminationStep 2
    40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
    canonicalSparseTraceR01C01Factors9 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 9).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors10 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step9.afterFactors

def canonicalSparseTraceR01C01Step10 : CheckedScopedEliminationStep 2
    47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
    canonicalSparseTraceR01C01Factors10 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 10).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors11 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step10.afterFactors

def canonicalSparseTraceR01C01Step11 : CheckedScopedEliminationStep 2
    50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
    canonicalSparseTraceR01C01Factors11 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 11).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors12 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step11.afterFactors

theorem canonicalSparseTraceR01C01Shard02_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8)
        canonicalSparseTraceR01C01Factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        canonicalSparseTraceR01C01Factors12 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 9)
        canonicalSparseTraceR01C01Factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step8.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 10)
        canonicalSparseTraceR01C01Factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step9.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 11)
        canonicalSparseTraceR01C01Factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step10.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        canonicalSparseTraceR01C01Factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard02.canonicalSparseTraceR01C01Shard02_partitionSum_eqv
