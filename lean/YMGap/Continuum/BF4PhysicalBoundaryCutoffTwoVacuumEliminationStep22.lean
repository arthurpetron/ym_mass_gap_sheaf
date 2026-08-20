/- Exact certificate for cutoff-two elimination step 22. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep21
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step22Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 22).factor 2

def step22Bucket : List ScopedQFactor := factorBucket 37 factors22

theorem step22_table_checked :
    boundedLocalEquationCheck 2 step22Result.scope step22Result.value
      (eliminatedBucketValue 2 37 step22Bucket) = true := by
  decide

theorem step22_scope_nodup : step22Result.scope.Nodup := by decide
theorem step22_coordinate_not_scope : 37 ∉ step22Result.scope := by decide

theorem step22_scope_cover_checked :
    step22Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 37 ∨ id ∈ step22Result.scope)) = true := by
  decide

theorem step22_result_scope_remaining_checked :
    step22Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 23)) = true := by
  decide

def step22 : CheckedScopedEliminationStep 2 37
    (cutoffTwoVacuumEliminationFaceOrder.drop 23) factors22 where
  bucketResult :=
    { result := step22Result
      scope_nodup := step22_scope_nodup
      coordinate_not_scope := step22_coordinate_not_scope
      scope_cover_checked := step22_scope_cover_checked
      table_checked := step22_table_checked }
  result_scope_remaining_checked := step22_result_scope_remaining_checked

def factors23 : List ScopedQFactor := step22.afterFactors

theorem step22_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 22) factors22 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 23) factors23 :=
  step22.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22.step22_partitionSum_eqv

