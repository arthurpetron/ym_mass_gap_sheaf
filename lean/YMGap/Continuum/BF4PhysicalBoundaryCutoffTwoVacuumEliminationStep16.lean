/- Composed exact certificate for cutoff-two elimination step 16. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16Chunk02

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step16ChunkCertificate03 :
    ChunkedListAll step16ChunkSize step16Predicate (step16Tail 3) :=
  .done step16_tail_03_empty

def step16ChunkCertificate02 :
    ChunkedListAll step16ChunkSize step16Predicate (step16Tail 2) :=
  .step step16_chunk_02 step16ChunkCertificate03

def step16ChunkCertificate01 :
    ChunkedListAll step16ChunkSize step16Predicate (step16Tail 1) :=
  .step step16_chunk_01 step16ChunkCertificate02

def step16ChunkCertificate00 :
    ChunkedListAll step16ChunkSize step16Predicate (step16Tail 0) :=
  .step step16_chunk_00 step16ChunkCertificate01

theorem step16_table_checked :
    boundedLocalEquationCheck 2 step16Result.scope step16Result.value
      (eliminatedBucketValue 2 55 step16Bucket) = true :=
  step16ChunkCertificate00.all_eq_true

theorem step16_scope_nodup : step16Result.scope.Nodup := by decide
theorem step16_coordinate_not_scope : 55 ∉ step16Result.scope := by decide

theorem step16_scope_cover_checked :
    step16Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 55 ∨ id ∈ step16Result.scope)) = true := by
  decide

theorem step16_result_scope_remaining_checked :
    step16Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 17)) = true := by
  decide

def step16 : CheckedScopedEliminationStep 2 55
    (cutoffTwoVacuumEliminationFaceOrder.drop 17) factors16 where
  bucketResult :=
    { result := step16Result
      scope_nodup := step16_scope_nodup
      coordinate_not_scope := step16_coordinate_not_scope
      scope_cover_checked := step16_scope_cover_checked
      table_checked := step16_table_checked }
  result_scope_remaining_checked := step16_result_scope_remaining_checked

def factors17 : List ScopedQFactor := step16.afterFactors

theorem step16_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 16) factors16 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 17) factors17 :=
  step16.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep16.step16_partitionSum_eqv
