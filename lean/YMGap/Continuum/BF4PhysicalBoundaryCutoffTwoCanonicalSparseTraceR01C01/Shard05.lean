/- Generated canonical sparse trace R01C01, shard 5. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard04

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard05

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard04

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Step20 : CheckedScopedEliminationStep 2
    59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
    canonicalSparseTraceR01C01Factors20 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 20).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors21 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step20.afterFactors

def canonicalSparseTraceR01C01Step21 : CheckedScopedEliminationStep 2
    49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
    canonicalSparseTraceR01C01Factors21 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 21).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors22 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step21.afterFactors

def canonicalSparseTraceR01C01Step22 : CheckedScopedEliminationStep 2
    68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
    canonicalSparseTraceR01C01Factors22 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 22).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors23 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step22.afterFactors

def canonicalSparseTraceR01C01Step23 : CheckedScopedEliminationStep 2
    67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
    canonicalSparseTraceR01C01Factors23 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 23).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors24 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step23.afterFactors

theorem canonicalSparseTraceR01C01Shard05_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        canonicalSparseTraceR01C01Factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        canonicalSparseTraceR01C01Factors24 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 21)
        canonicalSparseTraceR01C01Factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step20.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 22)
        canonicalSparseTraceR01C01Factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step21.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 23)
        canonicalSparseTraceR01C01Factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step22.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        canonicalSparseTraceR01C01Factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard05.canonicalSparseTraceR01C01Shard05_partitionSum_eqv
