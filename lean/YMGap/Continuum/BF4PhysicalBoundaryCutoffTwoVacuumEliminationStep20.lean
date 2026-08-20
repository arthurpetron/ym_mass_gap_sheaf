/- Exact certificate for cutoff-two elimination step 20. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step20Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 20).factor 2

def step20Bucket : List ScopedQFactor := factorBucket 45 factors20

theorem step20_table_checked :
    boundedLocalEquationCheck 2 step20Result.scope step20Result.value
      (eliminatedBucketValue 2 45 step20Bucket) = true := by
  decide

theorem step20_scope_nodup : step20Result.scope.Nodup := by decide
theorem step20_coordinate_not_scope : 45 ∉ step20Result.scope := by decide

theorem step20_scope_cover_checked :
    step20Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 45 ∨ id ∈ step20Result.scope)) = true := by
  decide

theorem step20_result_scope_remaining_checked :
    step20Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 21)) = true := by
  decide

def step20 : CheckedScopedEliminationStep 2 45
    (cutoffTwoVacuumEliminationFaceOrder.drop 21) factors20 where
  bucketResult :=
    { result := step20Result
      scope_nodup := step20_scope_nodup
      coordinate_not_scope := step20_coordinate_not_scope
      scope_cover_checked := step20_scope_cover_checked
      table_checked := step20_table_checked }
  result_scope_remaining_checked := step20_result_scope_remaining_checked

def factors21 : List ScopedQFactor := step20.afterFactors

theorem step20_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 20) factors20 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 21) factors21 :=
  step20.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep20.step20_partitionSum_eqv

