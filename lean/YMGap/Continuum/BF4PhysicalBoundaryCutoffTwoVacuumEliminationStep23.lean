/- Exact certificate for cutoff-two elimination step 23. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep22
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step23Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 23).factor 2

def step23Bucket : List ScopedQFactor := factorBucket 48 factors23

theorem step23_table_checked :
    boundedLocalEquationCheck 2 step23Result.scope step23Result.value
      (eliminatedBucketValue 2 48 step23Bucket) = true := by
  decide

theorem step23_scope_nodup : step23Result.scope.Nodup := by decide
theorem step23_coordinate_not_scope : 48 ∉ step23Result.scope := by decide

theorem step23_scope_cover_checked :
    step23Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 48 ∨ id ∈ step23Result.scope)) = true := by
  decide

theorem step23_result_scope_remaining_checked :
    step23Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 24)) = true := by
  decide

def step23 : CheckedScopedEliminationStep 2 48
    (cutoffTwoVacuumEliminationFaceOrder.drop 24) factors23 where
  bucketResult :=
    { result := step23Result
      scope_nodup := step23_scope_nodup
      coordinate_not_scope := step23_coordinate_not_scope
      scope_cover_checked := step23_scope_cover_checked
      table_checked := step23_table_checked }
  result_scope_remaining_checked := step23_result_scope_remaining_checked

def factors24 : List ScopedQFactor := step23.afterFactors

theorem step23_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 23) factors23 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 24) factors24 :=
  step23.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep23.step23_partitionSum_eqv

