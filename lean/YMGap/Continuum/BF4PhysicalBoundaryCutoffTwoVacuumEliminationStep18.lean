/- Exact certificate for cutoff-two elimination step 18. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step18Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 18).factor 2

def step18Bucket : List ScopedQFactor := factorBucket 39 factors18

theorem step18_table_checked :
    boundedLocalEquationCheck 2 step18Result.scope step18Result.value
      (eliminatedBucketValue 2 39 step18Bucket) = true := by
  decide

theorem step18_scope_nodup : step18Result.scope.Nodup := by decide
theorem step18_coordinate_not_scope : 39 ∉ step18Result.scope := by decide

theorem step18_scope_cover_checked :
    step18Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 39 ∨ id ∈ step18Result.scope)) = true := by
  decide

theorem step18_result_scope_remaining_checked :
    step18Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 19)) = true := by
  decide

def step18 : CheckedScopedEliminationStep 2 39
    (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors18 where
  bucketResult :=
    { result := step18Result
      scope_nodup := step18_scope_nodup
      coordinate_not_scope := step18_coordinate_not_scope
      scope_cover_checked := step18_scope_cover_checked
      table_checked := step18_table_checked }
  result_scope_remaining_checked := step18_result_scope_remaining_checked

def factors19 : List ScopedQFactor := step18.afterFactors

theorem step18_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 18) factors18 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 :=
  step18.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18.step18_partitionSum_eqv

