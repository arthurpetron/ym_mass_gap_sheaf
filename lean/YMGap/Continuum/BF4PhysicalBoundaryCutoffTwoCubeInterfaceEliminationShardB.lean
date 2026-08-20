/-
# Cutoff-two cube interface elimination shard B

This module checks sparse bucket equations 4 through 7 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationData
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardA

local infix:50 " ≈ " => Q'.eqv

def step4 : CheckedScopedEliminationStep 2 31
    (cutoffTwoCubeInterfaceEliminationOrder.drop 5) factors4 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 4).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors5 : List ScopedQFactor := step4.afterFactors

def step5 : CheckedScopedEliminationStep 2 32
    (cutoffTwoCubeInterfaceEliminationOrder.drop 6) factors5 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 5).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors6 : List ScopedQFactor := step5.afterFactors

def step6 : CheckedScopedEliminationStep 2 56
    (cutoffTwoCubeInterfaceEliminationOrder.drop 7) factors6 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 6).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors7 : List ScopedQFactor := step6.afterFactors

def step7 : CheckedScopedEliminationStep 2 58
    (cutoffTwoCubeInterfaceEliminationOrder.drop 8) factors7 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 7).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors8 : List ScopedQFactor := step7.afterFactors

theorem shardB_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4) factors4 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 8) factors8 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 4) factors4 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 5) factors5 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step4.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 6) factors6 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step5.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 7) factors7 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step6.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 8) factors8 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step7.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardB.shardB_partitionSum_eqv
