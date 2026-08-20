/- Exact certificate for cutoff-two elimination step 17. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step17Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 17).factor 2

def step17Bucket : List ScopedQFactor := factorBucket 9 factors17

theorem step17_table_checked :
    boundedLocalEquationCheck 2 step17Result.scope step17Result.value
      (eliminatedBucketValue 2 9 step17Bucket) = true := by
  decide

theorem step17_scope_nodup : step17Result.scope.Nodup := by decide
theorem step17_coordinate_not_scope : 9 ∉ step17Result.scope := by decide

theorem step17_scope_cover_checked :
    step17Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 9 ∨ id ∈ step17Result.scope)) = true := by
  decide

theorem step17_result_scope_remaining_checked :
    step17Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 18)) = true := by
  decide

def step17 : CheckedScopedEliminationStep 2 9
    (cutoffTwoVacuumEliminationFaceOrder.drop 18) factors17 where
  bucketResult :=
    { result := step17Result
      scope_nodup := step17_scope_nodup
      coordinate_not_scope := step17_coordinate_not_scope
      scope_cover_checked := step17_scope_cover_checked
      table_checked := step17_table_checked }
  result_scope_remaining_checked := step17_result_scope_remaining_checked

def factors18 : List ScopedQFactor := step17.afterFactors

theorem step17_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 17) factors17 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 18) factors18 :=
  step17.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep17.step17_partitionSum_eqv

