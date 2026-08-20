/-
# Cutoff-two vacuum-column elimination, certified step 10

Composes the independently compiled 729-assignment leaves into the exact
step-10 bucket certificate.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Chunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationTrace
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationShardB
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

def step10ChunkCertificate27 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 27) :=
  .done step10_tail_27_empty

def step10ChunkCertificate26 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 26) :=
  .step step10_chunk_26 step10ChunkCertificate27

def step10ChunkCertificate25 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 25) :=
  .step step10_chunk_25 step10ChunkCertificate26

def step10ChunkCertificate24 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 24) :=
  .step step10_chunk_24 step10ChunkCertificate25

def step10ChunkCertificate23 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 23) :=
  .step step10_chunk_23 step10ChunkCertificate24

def step10ChunkCertificate22 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 22) :=
  .step step10_chunk_22 step10ChunkCertificate23

def step10ChunkCertificate21 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 21) :=
  .step step10_chunk_21 step10ChunkCertificate22

def step10ChunkCertificate20 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 20) :=
  .step step10_chunk_20 step10ChunkCertificate21

def step10ChunkCertificate19 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 19) :=
  .step step10_chunk_19 step10ChunkCertificate20

def step10ChunkCertificate18 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 18) :=
  .step step10_chunk_18 step10ChunkCertificate19

def step10ChunkCertificate17 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 17) :=
  .step step10_chunk_17 step10ChunkCertificate18

def step10ChunkCertificate16 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 16) :=
  .step step10_chunk_16 step10ChunkCertificate17

def step10ChunkCertificate15 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 15) :=
  .step step10_chunk_15 step10ChunkCertificate16

def step10ChunkCertificate14 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 14) :=
  .step step10_chunk_14 step10ChunkCertificate15

def step10ChunkCertificate13 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 13) :=
  .step step10_chunk_13 step10ChunkCertificate14

def step10ChunkCertificate12 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 12) :=
  .step step10_chunk_12 step10ChunkCertificate13

def step10ChunkCertificate11 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 11) :=
  .step step10_chunk_11 step10ChunkCertificate12

def step10ChunkCertificate10 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 10) :=
  .step step10_chunk_10 step10ChunkCertificate11

def step10ChunkCertificate09 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 9) :=
  .step step10_chunk_09 step10ChunkCertificate10

def step10ChunkCertificate08 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 8) :=
  .step step10_chunk_08 step10ChunkCertificate09

def step10ChunkCertificate07 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 7) :=
  .step step10_chunk_07 step10ChunkCertificate08

def step10ChunkCertificate06 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 6) :=
  .step step10_chunk_06 step10ChunkCertificate07

def step10ChunkCertificate05 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 5) :=
  .step step10_chunk_05 step10ChunkCertificate06

def step10ChunkCertificate04 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 4) :=
  .step step10_chunk_04 step10ChunkCertificate05

def step10ChunkCertificate03 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 3) :=
  .step step10_chunk_03 step10ChunkCertificate04

def step10ChunkCertificate02 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 2) :=
  .step step10_chunk_02 step10ChunkCertificate03

def step10ChunkCertificate01 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 1) :=
  .step step10_chunk_01 step10ChunkCertificate02

def step10ChunkCertificate00 :
    ChunkedListAll step10ChunkSize step10Predicate (step10Tail 0) :=
  .step step10_chunk_00 step10ChunkCertificate01

theorem step10_table_checked :
    boundedLocalEquationCheck 2 step10Result.scope step10Result.value
      (eliminatedBucketValue 2 0 step10Bucket) = true := by
  exact step10ChunkCertificate00.all_eq_true

theorem step10_scope_nodup : step10Result.scope.Nodup := by decide

theorem step10_coordinate_not_scope : 0 ∉ step10Result.scope := by decide

theorem step10_scope_cover_checked :
    step10Bucket.all (fun factor =>
      factor.scope.all fun id =>
        decide (id = 0 ∨ id ∈ step10Result.scope)) = true := by
  decide

theorem step10_result_scope_remaining_checked :
    step10Result.scope.all (fun id =>
      decide (id ∈ cutoffTwoVacuumEliminationFaceOrder.drop 11)) = true := by
  decide

def step10 : CheckedScopedEliminationStep 2 0
    (cutoffTwoVacuumEliminationFaceOrder.drop 11) factors10 where
  bucketResult :=
    { result := step10Result
      scope_nodup := step10_scope_nodup
      coordinate_not_scope := step10_coordinate_not_scope
      scope_cover_checked := step10_scope_cover_checked
      table_checked := step10_table_checked }
  result_scope_remaining_checked := step10_result_scope_remaining_checked

def factors11 : List ScopedQFactor := step10.afterFactors

theorem step10_partitionSum_eqv :
    scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 10) factors10 ≈
      scopedFactorPartitionSum 2
        (cutoffTwoVacuumEliminationFaceOrder.drop 11) factors11 := by
  exact step10.partitionSum_eqv_after

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10.step10_partitionSum_eqv

