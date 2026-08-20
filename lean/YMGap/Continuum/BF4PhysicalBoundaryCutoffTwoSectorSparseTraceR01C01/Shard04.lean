/- Generated sparse trace R01C01, shard 4. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01.Shard03

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard04

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard03

local infix:50 " ≈ " => Q'.eqv

def sparseTraceR01C01Step16 : CheckedScopedEliminationStep 2
    11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
    sparseTraceR01C01Factors16 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 16).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sparseTraceR01C01Factors17 : List ScopedQFactor :=
  sparseTraceR01C01Step16.afterFactors

def sparseTraceR01C01Step17 : CheckedScopedEliminationStep 2
    20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
    sparseTraceR01C01Factors17 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 17).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sparseTraceR01C01Factors18 : List ScopedQFactor :=
  sparseTraceR01C01Step17.afterFactors

def sparseTraceR01C01Step18 : CheckedScopedEliminationStep 2
    65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
    sparseTraceR01C01Factors18 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 18).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sparseTraceR01C01Factors19 : List ScopedQFactor :=
  sparseTraceR01C01Step18.afterFactors

def sparseTraceR01C01Step19 : CheckedScopedEliminationStep 2
    29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
    sparseTraceR01C01Factors19 where
  bucketResult :=
    { result := (sparseTraceR01C01Datum 19).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def sparseTraceR01C01Factors20 : List ScopedQFactor :=
  sparseTraceR01C01Step19.afterFactors

theorem sparseTraceR01C01Shard04_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16)
        sparseTraceR01C01Factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        sparseTraceR01C01Factors20 := by
  calc
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 17)
        sparseTraceR01C01Factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sparseTraceR01C01Step16.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 18)
        sparseTraceR01C01Factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sparseTraceR01C01Step17.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 19)
        sparseTraceR01C01Factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sparseTraceR01C01Step18.partitionSum_eqv_after
    _ ≈ scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20)
        sparseTraceR01C01Factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        sparseTraceR01C01Step19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard04

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorSparseTraceR01C01Shard04.sparseTraceR01C01Shard04_partitionSum_eqv
