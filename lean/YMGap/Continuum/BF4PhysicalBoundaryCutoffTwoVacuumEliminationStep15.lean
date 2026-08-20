/- Composed exact certificate for cutoff-two elimination step 15. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Chunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step15ChunkCertificate09 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 9) :=
  .done step15_tail_09_empty

def step15ChunkCertificate08 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 8) :=
  .step step15_chunk_08 step15ChunkCertificate09

def step15ChunkCertificate07 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 7) :=
  .step step15_chunk_07 step15ChunkCertificate08

def step15ChunkCertificate06 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 6) :=
  .step step15_chunk_06 step15ChunkCertificate07

def step15ChunkCertificate05 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 5) :=
  .step step15_chunk_05 step15ChunkCertificate06

def step15ChunkCertificate04 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 4) :=
  .step step15_chunk_04 step15ChunkCertificate05

def step15ChunkCertificate03 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 3) :=
  .step step15_chunk_03 step15ChunkCertificate04

def step15ChunkCertificate02 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 2) :=
  .step step15_chunk_02 step15ChunkCertificate03

def step15ChunkCertificate01 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 1) :=
  .step step15_chunk_01 step15ChunkCertificate02

def step15ChunkCertificate00 :
    ChunkedListAll step15ChunkSize step15Predicate (step15Tail 0) :=
  .step step15_chunk_00 step15ChunkCertificate01

theorem step15_table_checked :
    boundedLocalEquationCheck 2 step15Result.scope step15Result.value
      (eliminatedBucketValue 2 57 step15Bucket) = true :=
  step15ChunkCertificate00.all_eq_true

theorem step15_scope_nodup : step15Result.scope.Nodup := by decide
theorem step15_coordinate_not_scope : 57 ∉ step15Result.scope := by decide

theorem step15_scope_cover_checked :
    step15Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 57 ∨ id ∈ step15Result.scope)) = true := by
  decide

theorem step15_result_scope_remaining_checked :
    step15Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 16)) = true := by
  decide

def step15 : CheckedScopedEliminationStep 2 57
    (cutoffTwoVacuumEliminationFaceOrder.drop 16) factors15 where
  bucketResult :=
    { result := step15Result
      scope_nodup := step15_scope_nodup
      coordinate_not_scope := step15_coordinate_not_scope
      scope_cover_checked := step15_scope_cover_checked
      table_checked := step15_table_checked }
  result_scope_remaining_checked := step15_result_scope_remaining_checked

def factors16 : List ScopedQFactor := step15.afterFactors

theorem step15_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 15) factors15 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 16) factors16 :=
  step15.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15.step15_partitionSum_eqv
