/-
# Cutoff-two cube interface elimination shard F

This module checks sparse bucket equations 20 through 23 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardF

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
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE

local infix:50 " ≈ " => Q'.eqv

def step20 : CheckedScopedEliminationStep 2 59
    (cutoffTwoCubeInterfaceEliminationOrder.drop 21) factors20 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 20).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors21 : List ScopedQFactor := step20.afterFactors

def step21 : CheckedScopedEliminationStep 2 49
    (cutoffTwoCubeInterfaceEliminationOrder.drop 22) factors21 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 21).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors22 : List ScopedQFactor := step21.afterFactors

def step22 : CheckedScopedEliminationStep 2 68
    (cutoffTwoCubeInterfaceEliminationOrder.drop 23) factors22 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 22).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors23 : List ScopedQFactor := step22.afterFactors

def step23 : CheckedScopedEliminationStep 2 67
    (cutoffTwoCubeInterfaceEliminationOrder.drop 24) factors23 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 23).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors24 : List ScopedQFactor := step23.afterFactors

theorem shardF_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20) factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24) factors24 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20) factors20 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 21) factors21 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step20.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 22) factors22 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step21.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 23) factors23 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step22.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 24) factors24 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardF

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardF.shardF_partitionSum_eqv
