/-
# Cutoff-two vacuum-column elimination, shard A

The first five sparse bucket equations are checked independently so Lean can
release their finite evaluation state before later shards are compiled.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def factors0 : List ScopedQFactor := cutoffTwoVacuumInitialFactors

def step0 : CheckedScopedEliminationStep 2 30
    (cutoffTwoVacuumEliminationFaceOrder.drop 1) factors0 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 0).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors1 : List ScopedQFactor := step0.afterFactors

def step1 : CheckedScopedEliminationStep 2 46
    (cutoffTwoVacuumEliminationFaceOrder.drop 2) factors1 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 1).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors2 : List ScopedQFactor := step1.afterFactors

def step2 : CheckedScopedEliminationStep 2 54
    (cutoffTwoVacuumEliminationFaceOrder.drop 3) factors2 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 2).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors3 : List ScopedQFactor := step2.afterFactors

def step3 : CheckedScopedEliminationStep 2 63
    (cutoffTwoVacuumEliminationFaceOrder.drop 4) factors3 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 3).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors4 : List ScopedQFactor := step3.afterFactors

def step4 : CheckedScopedEliminationStep 2 3
    (cutoffTwoVacuumEliminationFaceOrder.drop 5) factors4 where
  bucketResult :=
    { result := (cutoffTwoVacuumEliminationDatum 4).factor 2
      scope_nodup := by decide
      coordinate_not_scope := by decide
      scope_cover_checked := by decide
      table_checked := by decide }
  result_scope_remaining_checked := by decide

def factors5 : List ScopedQFactor := step4.afterFactors

theorem shardA_partitionSum_eqv :
    scopedFactorPartitionSum 2
        cutoffTwoVacuumEliminationFaceOrder factors0 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 5) factors5 := by
  exact Q'.eqv_trans _ _ _
    (by simpa [cutoffTwoVacuumEliminationFaceOrder] using
      step0.partitionSum_eqv_after)
    (Q'.eqv_trans _ _ _ step1.partitionSum_eqv_after
      (Q'.eqv_trans _ _ _ step2.partitionSum_eqv_after
        (Q'.eqv_trans _ _ _ step3.partitionSum_eqv_after
          step4.partitionSum_eqv_after)))

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardA.shardA_partitionSum_eqv
