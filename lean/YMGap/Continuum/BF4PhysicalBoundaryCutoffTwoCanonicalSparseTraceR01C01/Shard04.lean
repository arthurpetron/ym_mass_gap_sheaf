/- Generated canonical sparse trace R01C01, shard 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard03

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard04

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard03

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Step16 : CheckedScopedEliminationStep 2
    11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    canonicalSparseTraceR01C01Factors16 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 16).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors17 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step16.afterFactors

def canonicalSparseTraceR01C01Step17 : CheckedScopedEliminationStep 2
    20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    canonicalSparseTraceR01C01Factors17 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 17).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors18 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step17.afterFactors

def canonicalSparseTraceR01C01Step18 : CheckedScopedEliminationStep 2
    65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    canonicalSparseTraceR01C01Factors18 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 18).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors19 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step18.afterFactors

def canonicalSparseTraceR01C01Step19 : CheckedScopedEliminationStep 2
    29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    canonicalSparseTraceR01C01Factors19 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 19).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors20 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step19.afterFactors

theorem canonicalSparseTraceR01C01Shard04_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        canonicalSparseTraceR01C01Factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        canonicalSparseTraceR01C01Factors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        canonicalSparseTraceR01C01Factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        canonicalSparseTraceR01C01Factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        canonicalSparseTraceR01C01Factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        canonicalSparseTraceR01C01Factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard04

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard04.canonicalSparseTraceR01C01Shard04_partitionSum_eqv
