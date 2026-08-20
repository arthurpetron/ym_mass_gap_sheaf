/-
# Cutoff-two cube interface elimination shard E

This module checks sparse bucket equations 16 through 19 independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardD

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE

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

local infix:50 " ≈ " => Q'.eqv

def step16 : CheckedScopedEliminationStep 2 11
    (cutoffTwoCubeInterfaceEliminationOrder.drop 17) factors16 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 16).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors17 : List ScopedQFactor := step16.afterFactors

def step17 : CheckedScopedEliminationStep 2 20
    (cutoffTwoCubeInterfaceEliminationOrder.drop 18) factors17 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 17).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors18 : List ScopedQFactor := step17.afterFactors

def step18 : CheckedScopedEliminationStep 2 65
    (cutoffTwoCubeInterfaceEliminationOrder.drop 19) factors18 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 18).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors19 : List ScopedQFactor := step18.afterFactors

def step19 : CheckedScopedEliminationStep 2 29
    (cutoffTwoCubeInterfaceEliminationOrder.drop 20) factors19 where
  bucketResult :=
    { result := (cutoffTwoCubeInterfaceEliminationDatum 19).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors20 : List ScopedQFactor := step19.afterFactors

theorem shardE_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16) factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 20) factors20 := by
  calc
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 16) factors16 ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 17) factors17 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step16.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 18) factors18 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step17.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 19) factors19 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step18.partitionSum_eqv_after
    _ ≈
        scopedFactorPartitionSum 2
          (cutoffTwoCubeInterfaceEliminationOrder.drop 20) factors20 := by
      simpa [cutoffTwoCubeInterfaceEliminationOrder] using
        step19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceEliminationShardE.shardE_partitionSum_eqv
