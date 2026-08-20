/- Generated canonical sparse trace R01C01, shard 0. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard00

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Factors0 : List ScopedQFactor :=
  cutoffTwoCanonicalSectorPairFactors 1 1

def canonicalSparseTraceR01C01Step0 : CheckedScopedEliminationStep 2
    38
    (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
    canonicalSparseTraceR01C01Factors0 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 0).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors1 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step0.afterFactors

def canonicalSparseTraceR01C01Step1 : CheckedScopedEliminationStep 2
    22
    (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
    canonicalSparseTraceR01C01Factors1 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 1).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors2 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step1.afterFactors

def canonicalSparseTraceR01C01Step2 : CheckedScopedEliminationStep 2
    14
    (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
    canonicalSparseTraceR01C01Factors2 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 2).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors3 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step2.afterFactors

def canonicalSparseTraceR01C01Step3 : CheckedScopedEliminationStep 2
    5
    (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
    canonicalSparseTraceR01C01Factors3 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 3).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors4 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step3.afterFactors

theorem canonicalSparseTraceR01C01Shard00_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 0)
        canonicalSparseTraceR01C01Factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        canonicalSparseTraceR01C01Factors4 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 1)
        canonicalSparseTraceR01C01Factors1 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step0.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 2)
        canonicalSparseTraceR01C01Factors2 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step1.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 3)
        canonicalSparseTraceR01C01Factors3 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step2.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4)
        canonicalSparseTraceR01C01Factors4 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step3.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard00

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard00.canonicalSparseTraceR01C01Shard00_partitionSum_eqv
