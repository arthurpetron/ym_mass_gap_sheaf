/-
# Cutoff-two cube interface elimination shard C

This module checks sparse bucket equations 8 through 11 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB

local infix:50 " ≈ " => Q'.eqv

def step8 : CheckedScopedEliminationStep 2 23
    (cutoffTwoCubeInterfaceEliminationOrder.drop 9) factors8 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 8).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors9 : List ScopedQFactor := step8.afterFactors

def step9 : CheckedScopedEliminationStep 2 40
    (cutoffTwoCubeInterfaceEliminationOrder.drop 10) factors9 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 9).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors10 : List ScopedQFactor := step9.afterFactors

def step10 : CheckedScopedEliminationStep 2 47
    (cutoffTwoCubeInterfaceEliminationOrder.drop 11) factors10 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 10).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors11 : List ScopedQFactor := step10.afterFactors

def step11 : CheckedScopedEliminationStep 2 50
    (cutoffTwoCubeInterfaceEliminationOrder.drop 12) factors11 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 11).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors12 : List ScopedQFactor := step11.afterFactors

theorem shardC_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8) factors8 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12) factors12 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8) factors8 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 9) factors9 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step8.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 10) factors10 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step9.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 11) factors11 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step10.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 12) factors12 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC.shardC_partitionSum_eqv
