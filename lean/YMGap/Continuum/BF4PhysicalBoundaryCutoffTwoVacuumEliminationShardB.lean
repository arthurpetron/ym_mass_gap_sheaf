/-
# Cutoff-two vacuum-column elimination, shard B

Sparse bucket steps five through nine, compiled independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step5 : CheckedScopedEliminationStep 2 10
    (cutoffTwoVacuumEliminationFaceOrder.drop 6) factors5 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 5).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors6 : List ScopedQFactor := step5.afterFactors

def step6 : CheckedScopedEliminationStep 2 36
    (cutoffTwoVacuumEliminationFaceOrder.drop 7) factors6 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 6).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors7 : List ScopedQFactor := step6.afterFactors

def step7 : CheckedScopedEliminationStep 2 18
    (cutoffTwoVacuumEliminationFaceOrder.drop 8) factors7 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 7).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors8 : List ScopedQFactor := step7.afterFactors

def step8 : CheckedScopedEliminationStep 2 64
    (cutoffTwoVacuumEliminationFaceOrder.drop 9) factors8 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 8).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors9 : List ScopedQFactor := step8.afterFactors

def step9 : CheckedScopedEliminationStep 2 66
    (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors9 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 9).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors10 : List ScopedQFactor := step9.afterFactors

theorem shardB_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 5) factors5 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors10 := by
  exact Q'.eqv_trans _ _ _
    (by simpa [cutoffTwoVacuumEliminationFaceOrder] using
      step5.partitionSum_eqv_after)
    (Q'.eqv_trans _ _ _ step6.partitionSum_eqv_after
      (Q'.eqv_trans _ _ _ step7.partitionSum_eqv_after
        (Q'.eqv_trans _ _ _ step8.partitionSum_eqv_after
          step9.partitionSum_eqv_after)))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB.shardB_partitionSum_eqv
