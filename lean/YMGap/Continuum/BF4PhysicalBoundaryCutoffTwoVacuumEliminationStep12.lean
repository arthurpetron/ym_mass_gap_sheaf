/- Composed exact certificate for cutoff-two elimination step 12. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Chunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step12ChunkCertificate09 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 9) :=
  .done step12_tail_09_empty

def step12ChunkCertificate08 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 8) :=
  .step step12_chunk_08 step12ChunkCertificate09

def step12ChunkCertificate07 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 7) :=
  .step step12_chunk_07 step12ChunkCertificate08

def step12ChunkCertificate06 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 6) :=
  .step step12_chunk_06 step12ChunkCertificate07

def step12ChunkCertificate05 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 5) :=
  .step step12_chunk_05 step12ChunkCertificate06

def step12ChunkCertificate04 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 4) :=
  .step step12_chunk_04 step12ChunkCertificate05

def step12ChunkCertificate03 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 3) :=
  .step step12_chunk_03 step12ChunkCertificate04

def step12ChunkCertificate02 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 2) :=
  .step step12_chunk_02 step12ChunkCertificate03

def step12ChunkCertificate01 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 1) :=
  .step step12_chunk_01 step12ChunkCertificate02

def step12ChunkCertificate00 :
    ChunkedListAll step12ChunkSize step12Predicate (step12Tail 0) :=
  .step step12_chunk_00 step12ChunkCertificate01

theorem step12_table_checked :
    boundedLocalEquationCheck 2 step12Result.scope step12Result.value
      (eliminatedBucketValue 2 27 step12Bucket) = true :=
  step12ChunkCertificate00.all_eq_true

theorem step12_scope_nodup : step12Result.scope.Nodup := by decide
theorem step12_coordinate_not_scope : 27 ∉ step12Result.scope := by decide

theorem step12_scope_cover_checked :
    step12Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 27 ∨ id ∈ step12Result.scope)) = true := by
  decide

theorem step12_result_scope_remaining_checked :
    step12Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 13)) = true := by
  decide

def step12 : CheckedScopedEliminationStep 2 27
    (cutoffTwoVacuumEliminationFaceOrder.drop 13) factors12 where
  bucketResult :=
    { result := step12Result
      scope_nodup := step12_scope_nodup
      coordinate_not_scope := step12_coordinate_not_scope
      scope_cover_checked := step12_scope_cover_checked
      table_checked := step12_table_checked }
  result_scope_remaining_checked := step12_result_scope_remaining_checked

def factors13 : List ScopedQFactor := step12.afterFactors

theorem step12_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 12) factors12 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 13) factors13 :=
  step12.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12.step12_partitionSum_eqv

