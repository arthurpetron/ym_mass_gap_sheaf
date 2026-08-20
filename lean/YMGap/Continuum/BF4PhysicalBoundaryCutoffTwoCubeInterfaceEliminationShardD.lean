/-
# Cutoff-two cube interface elimination shard D

This module checks sparse bucket equations 12 through 15 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardC

local infix:50 " ≈ " => Q'.eqv

def step12 : CheckedScopedEliminationStep 2 13
    (cutoffTwoCubeInterfaceEliminationOrder.drop 13) factors12 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 12).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors13 : List ScopedQFactor := step12.afterFactors

def step13 : CheckedScopedEliminationStep 2 4
    (cutoffTwoCubeInterfaceEliminationOrder.drop 14) factors13 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 13).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors14 : List ScopedQFactor := step13.afterFactors

def step14 : CheckedScopedEliminationStep 2 41
    (cutoffTwoCubeInterfaceEliminationOrder.drop 15) factors14 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 14).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors15 : List ScopedQFactor := step14.afterFactors

def step15 : CheckedScopedEliminationStep 2 2
    (cutoffTwoCubeInterfaceEliminationOrder.drop 16) factors15 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 15).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors16 : List ScopedQFactor := step15.afterFactors

theorem shardD_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12) factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16) factors16 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 12) factors12 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 13) factors13 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step12.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 14) factors14 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step13.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 15) factors15 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step14.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 16) factors16 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD.shardD_partitionSum_eqv
