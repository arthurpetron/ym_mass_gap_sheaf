/- Generated canonical sparse trace R01C01, shard 3. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01.Shard02

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard03

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard02

local infix:50 " ≈ " => Q'.eqv

def canonicalSparseTraceR01C01Step12 : CheckedScopedEliminationStep 2
    13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
    canonicalSparseTraceR01C01Factors12 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 12).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors13 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step12.afterFactors

def canonicalSparseTraceR01C01Step13 : CheckedScopedEliminationStep 2
    4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
    canonicalSparseTraceR01C01Factors13 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 13).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors14 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step13.afterFactors

def canonicalSparseTraceR01C01Step14 : CheckedScopedEliminationStep 2
    41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
    canonicalSparseTraceR01C01Factors14 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 14).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors15 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step14.afterFactors

def canonicalSparseTraceR01C01Step15 : CheckedScopedEliminationStep 2
    2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
    canonicalSparseTraceR01C01Factors15 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 15).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def canonicalSparseTraceR01C01Factors16 : List ScopedQFactor :=
  canonicalSparseTraceR01C01Step15.afterFactors

theorem canonicalSparseTraceR01C01Shard03_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12)
        canonicalSparseTraceR01C01Factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        canonicalSparseTraceR01C01Factors16 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 13)
        canonicalSparseTraceR01C01Factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step12.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 14)
        canonicalSparseTraceR01C01Factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step13.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 15)
        canonicalSparseTraceR01C01Factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step14.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        canonicalSparseTraceR01C01Factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        canonicalSparseTraceR01C01Step15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSparseTraceR01C01Shard03.canonicalSparseTraceR01C01Shard03_partitionSum_eqv
