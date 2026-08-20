/- Exact certificate for cutoff-two elimination step 21. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step21Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 21).factor 2

def step21Bucket : List ScopedQFactor := factorBucket 12 factors21

theorem step21_table_checked :
    boundedLocalEquationCheck 2 step21Result.scope step21Result.value
      (eliminatedBucketValue 2 12 step21Bucket) = true := by
  decide

theorem step21_scope_nodup : step21Result.scope.Nodup := by decide
theorem step21_coordinate_not_scope : 12 ∉ step21Result.scope := by decide

theorem step21_scope_cover_checked :
    step21Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 12 ∨ id ∈ step21Result.scope)) = true := by
  decide

theorem step21_result_scope_remaining_checked :
    step21Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 22)) = true := by
  decide

def step21 : CheckedScopedEliminationStep 2 12
    (cutoffTwoVacuumEliminationFaceOrder.drop 22) factors21 where
  bucketResult :=
    { result := step21Result
      scope_nodup := step21_scope_nodup
      coordinate_not_scope := step21_coordinate_not_scope
      scope_cover_checked := step21_scope_cover_checked
      table_checked := step21_table_checked }
  result_scope_remaining_checked := step21_result_scope_remaining_checked

def factors22 : List ScopedQFactor := step21.afterFactors

theorem step21_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 21) factors21 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 22) factors22 :=
  step21.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21.step21_partitionSum_eqv

