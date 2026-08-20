/- Composed exact certificate for cutoff-two elimination step 14. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Chunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step14ChunkCertificate27 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 27) :=
  .done step14_tail_27_empty

def step14ChunkCertificate26 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 26) :=
  .step step14_chunk_26 step14ChunkCertificate27

def step14ChunkCertificate25 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 25) :=
  .step step14_chunk_25 step14ChunkCertificate26

def step14ChunkCertificate24 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 24) :=
  .step step14_chunk_24 step14ChunkCertificate25

def step14ChunkCertificate23 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 23) :=
  .step step14_chunk_23 step14ChunkCertificate24

def step14ChunkCertificate22 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 22) :=
  .step step14_chunk_22 step14ChunkCertificate23

def step14ChunkCertificate21 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 21) :=
  .step step14_chunk_21 step14ChunkCertificate22

def step14ChunkCertificate20 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 20) :=
  .step step14_chunk_20 step14ChunkCertificate21

def step14ChunkCertificate19 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 19) :=
  .step step14_chunk_19 step14ChunkCertificate20

def step14ChunkCertificate18 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 18) :=
  .step step14_chunk_18 step14ChunkCertificate19

def step14ChunkCertificate17 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 17) :=
  .step step14_chunk_17 step14ChunkCertificate18

def step14ChunkCertificate16 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 16) :=
  .step step14_chunk_16 step14ChunkCertificate17

def step14ChunkCertificate15 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 15) :=
  .step step14_chunk_15 step14ChunkCertificate16

def step14ChunkCertificate14 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 14) :=
  .step step14_chunk_14 step14ChunkCertificate15

def step14ChunkCertificate13 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 13) :=
  .step step14_chunk_13 step14ChunkCertificate14

def step14ChunkCertificate12 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 12) :=
  .step step14_chunk_12 step14ChunkCertificate13

def step14ChunkCertificate11 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 11) :=
  .step step14_chunk_11 step14ChunkCertificate12

def step14ChunkCertificate10 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 10) :=
  .step step14_chunk_10 step14ChunkCertificate11

def step14ChunkCertificate09 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 9) :=
  .step step14_chunk_09 step14ChunkCertificate10

def step14ChunkCertificate08 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 8) :=
  .step step14_chunk_08 step14ChunkCertificate09

def step14ChunkCertificate07 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 7) :=
  .step step14_chunk_07 step14ChunkCertificate08

def step14ChunkCertificate06 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 6) :=
  .step step14_chunk_06 step14ChunkCertificate07

def step14ChunkCertificate05 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 5) :=
  .step step14_chunk_05 step14ChunkCertificate06

def step14ChunkCertificate04 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 4) :=
  .step step14_chunk_04 step14ChunkCertificate05

def step14ChunkCertificate03 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 3) :=
  .step step14_chunk_03 step14ChunkCertificate04

def step14ChunkCertificate02 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 2) :=
  .step step14_chunk_02 step14ChunkCertificate03

def step14ChunkCertificate01 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 1) :=
  .step step14_chunk_01 step14ChunkCertificate02

def step14ChunkCertificate00 :
    ChunkedListAll step14ChunkSize step14Predicate (step14Tail 0) :=
  .step step14_chunk_00 step14ChunkCertificate01

theorem step14_table_checked :
    boundedLocalEquationCheck 2 step14Result.scope step14Result.value
      (eliminatedBucketValue 2 19 step14Bucket) = true :=
  step14ChunkCertificate00.all_eq_true

theorem step14_scope_nodup : step14Result.scope.Nodup := by decide
theorem step14_coordinate_not_scope : 19 ∉ step14Result.scope := by decide
theorem step14_scope_cover_checked :
    step14Bucket.all (fun factor => factor.scope.all fun id =>
      decide (id = 19 ∨ id ∈ step14Result.scope)) = true := by decide
theorem step14_result_scope_remaining_checked :
    step14Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 15)) = true := by decide

def step14 : CheckedScopedEliminationStep 2 19
    (cutoffTwoVacuumEliminationFaceOrder.drop 15) factors14 where
  bucketResult :=
    { result := step14Result
      scope_nodup := step14_scope_nodup
      coordinate_not_scope := step14_coordinate_not_scope
      scope_cover_checked := step14_scope_cover_checked
      table_checked := step14_table_checked }
  result_scope_remaining_checked := step14_result_scope_remaining_checked

def factors15 : List ScopedQFactor := step14.afterFactors

theorem step14_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 14) factors14 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 15) factors15 :=
  step14.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14.step14_partitionSum_eqv

