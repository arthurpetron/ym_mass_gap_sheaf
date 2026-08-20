/- Exact certificate for cutoff-two elimination step 19. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep18
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step19Result : ScopedQFactor :=
  (cutoffTwoVacuumEliminationDatum 19).factor 2

def step19Bucket : List ScopedQFactor := factorBucket 1 factors19

theorem step19_table_checked :
    boundedLocalEquationCheck 2 step19Result.scope step19Result.value
      (eliminatedBucketValue 2 1 step19Bucket) = true := by
  decide

theorem step19_scope_nodup : step19Result.scope.Nodup := by decide
theorem step19_coordinate_not_scope : 1 ∉ step19Result.scope := by decide

theorem step19_scope_cover_checked :
    step19Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 1 ∨ id ∈ step19Result.scope)) = true := by
  decide

theorem step19_result_scope_remaining_checked :
    step19Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 20)) = true := by
  decide

def step19 : CheckedScopedEliminationStep 2 1
    (cutoffTwoVacuumEliminationFaceOrder.drop 20) factors19 where
  bucketResult :=
    { result := step19Result
      scope_nodup := step19_scope_nodup
      coordinate_not_scope := step19_coordinate_not_scope
      scope_cover_checked := step19_scope_cover_checked
      table_checked := step19_table_checked }
  result_scope_remaining_checked := step19_result_scope_remaining_checked

def factors20 : List ScopedQFactor := step19.afterFactors

theorem step19_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 19) factors19 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 20) factors20 :=
  step19.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep19.step19_partitionSum_eqv

