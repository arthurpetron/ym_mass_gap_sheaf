/-
# Cutoff-two cube interface elimination shard A

This module checks sparse bucket equations 0 through 3 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def factors0 : List ScopedQFactor := cutoffTwoCubeInterfaceFactors

def step0 : CheckedScopedEliminationStep 2 38
    (cutoffTwoCubeInterfaceEliminationOrder.drop 1) factors0 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 0).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors1 : List ScopedQFactor := step0.afterFactors

def step1 : CheckedScopedEliminationStep 2 22
    (cutoffTwoCubeInterfaceEliminationOrder.drop 2) factors1 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 1).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors2 : List ScopedQFactor := step1.afterFactors

def step2 : CheckedScopedEliminationStep 2 14
    (cutoffTwoCubeInterfaceEliminationOrder.drop 3) factors2 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 2).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors3 : List ScopedQFactor := step2.afterFactors

def step3 : CheckedScopedEliminationStep 2 5
    (cutoffTwoCubeInterfaceEliminationOrder.drop 4) factors3 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 3).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors4 : List ScopedQFactor := step3.afterFactors

theorem shardA_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 0) factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4) factors4 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 0) factors0 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 1) factors1 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step0.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 2) factors2 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step1.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 3) factors3 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step2.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 4) factors4 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step3.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA.shardA_partitionSum_eqv
