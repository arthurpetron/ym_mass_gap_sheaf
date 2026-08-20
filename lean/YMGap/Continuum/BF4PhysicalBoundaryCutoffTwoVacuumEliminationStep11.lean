/- Composed exact certificate for cutoff-two elimination step 11. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11Chunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step11ChunkCertificate27 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 27) :=
  .done step11_tail_27_empty

def step11ChunkCertificate26 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 26) :=
  .step step11_chunk_26 step11ChunkCertificate27

def step11ChunkCertificate25 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 25) :=
  .step step11_chunk_25 step11ChunkCertificate26

def step11ChunkCertificate24 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 24) :=
  .step step11_chunk_24 step11ChunkCertificate25

def step11ChunkCertificate23 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 23) :=
  .step step11_chunk_23 step11ChunkCertificate24

def step11ChunkCertificate22 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 22) :=
  .step step11_chunk_22 step11ChunkCertificate23

def step11ChunkCertificate21 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 21) :=
  .step step11_chunk_21 step11ChunkCertificate22

def step11ChunkCertificate20 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 20) :=
  .step step11_chunk_20 step11ChunkCertificate21

def step11ChunkCertificate19 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 19) :=
  .step step11_chunk_19 step11ChunkCertificate20

def step11ChunkCertificate18 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 18) :=
  .step step11_chunk_18 step11ChunkCertificate19

def step11ChunkCertificate17 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 17) :=
  .step step11_chunk_17 step11ChunkCertificate18

def step11ChunkCertificate16 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 16) :=
  .step step11_chunk_16 step11ChunkCertificate17

def step11ChunkCertificate15 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 15) :=
  .step step11_chunk_15 step11ChunkCertificate16

def step11ChunkCertificate14 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 14) :=
  .step step11_chunk_14 step11ChunkCertificate15

def step11ChunkCertificate13 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 13) :=
  .step step11_chunk_13 step11ChunkCertificate14

def step11ChunkCertificate12 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 12) :=
  .step step11_chunk_12 step11ChunkCertificate13

def step11ChunkCertificate11 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 11) :=
  .step step11_chunk_11 step11ChunkCertificate12

def step11ChunkCertificate10 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 10) :=
  .step step11_chunk_10 step11ChunkCertificate11

def step11ChunkCertificate09 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 9) :=
  .step step11_chunk_09 step11ChunkCertificate10

def step11ChunkCertificate08 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 8) :=
  .step step11_chunk_08 step11ChunkCertificate09

def step11ChunkCertificate07 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 7) :=
  .step step11_chunk_07 step11ChunkCertificate08

def step11ChunkCertificate06 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 6) :=
  .step step11_chunk_06 step11ChunkCertificate07

def step11ChunkCertificate05 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 5) :=
  .step step11_chunk_05 step11ChunkCertificate06

def step11ChunkCertificate04 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 4) :=
  .step step11_chunk_04 step11ChunkCertificate05

def step11ChunkCertificate03 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 3) :=
  .step step11_chunk_03 step11ChunkCertificate04

def step11ChunkCertificate02 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 2) :=
  .step step11_chunk_02 step11ChunkCertificate03

def step11ChunkCertificate01 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 1) :=
  .step step11_chunk_01 step11ChunkCertificate02

def step11ChunkCertificate00 :
    ChunkedListAll step11ChunkSize step11Predicate (step11Tail 0) :=
  .step step11_chunk_00 step11ChunkCertificate01

theorem step11_table_checked :
    boundedLocalEquationCheck 2 step11Result.scope step11Result.value
      (eliminatedBucketValue 2 28 step11Bucket) = true :=
  step11ChunkCertificate00.all_eq_true

theorem step11_scope_nodup : step11Result.scope.Nodup := by decide
theorem step11_coordinate_not_scope : 28 ∉ step11Result.scope := by decide

theorem step11_scope_cover_checked :
    step11Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 28 ∨ id ∈ step11Result.scope)) = true := by
  decide

theorem step11_result_scope_remaining_checked :
    step11Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 12)) = true := by
  decide

def step11 : CheckedScopedEliminationStep 2 28
    (cutoffTwoVacuumEliminationFaceOrder.drop 12) factors11 where
  bucketResult :=
    { result := step11Result
      scope_nodup := step11_scope_nodup
      coordinate_not_scope := step11_coordinate_not_scope
      scope_cover_checked := step11_scope_cover_checked
      table_checked := step11_table_checked }
  result_scope_remaining_checked := step11_result_scope_remaining_checked

def factors12 : List ScopedQFactor := step11.afterFactors

theorem step11_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 11) factors11 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 12) factors12 :=
  step11.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep11.step11_partitionSum_eqv

