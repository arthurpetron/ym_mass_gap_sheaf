/-
# Kernel certificate for the cutoff-two arity-six multiplicity table

The 729-entry comparison is checked in nine independently compiled slices.
This module joins those equalities by the structural identity
`xs = xs.take 81 ++ xs.drop 81`; it does not rerun the monolithic table
comparison.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk08

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixCertificate

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk00
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk01
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk02
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk03
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk04
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk05
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk06
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk07
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk08

private theorem list_eq_of_take_eq_and_drop_eq
    {Item : Type} (chunkSize : Nat) {left right : List Item}
    (head_eq : left.take chunkSize = right.take chunkSize)
    (tail_eq : left.drop chunkSize = right.drop chunkSize) :
    left = right := by
  calc
    left = left.take chunkSize ++ left.drop chunkSize :=
      (List.take_append_drop chunkSize left).symm
    _ = right.take chunkSize ++ right.drop chunkSize := by
      rw [head_eq, tail_eq]
    _ = right := List.take_append_drop chunkSize right

private theorem cutoffTwoMultiplicityTableSix_tail_09 :
    cutoffTwoMultiplicityTableSixComputedTail 9 =
      cutoffTwoMultiplicityTableSixLiteralTail 9 := by
  decide

private theorem cutoffTwoMultiplicityTableSix_tail_08 :
    cutoffTwoMultiplicityTableSixComputedTail 8 =
      cutoffTwoMultiplicityTableSixLiteralTail 8 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_08
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_09

private theorem cutoffTwoMultiplicityTableSix_tail_07 :
    cutoffTwoMultiplicityTableSixComputedTail 7 =
      cutoffTwoMultiplicityTableSixLiteralTail 7 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_07
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_08

private theorem cutoffTwoMultiplicityTableSix_tail_06 :
    cutoffTwoMultiplicityTableSixComputedTail 6 =
      cutoffTwoMultiplicityTableSixLiteralTail 6 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_06
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_07

private theorem cutoffTwoMultiplicityTableSix_tail_05 :
    cutoffTwoMultiplicityTableSixComputedTail 5 =
      cutoffTwoMultiplicityTableSixLiteralTail 5 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_05
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_06

private theorem cutoffTwoMultiplicityTableSix_tail_04 :
    cutoffTwoMultiplicityTableSixComputedTail 4 =
      cutoffTwoMultiplicityTableSixLiteralTail 4 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_04
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_05

private theorem cutoffTwoMultiplicityTableSix_tail_03 :
    cutoffTwoMultiplicityTableSixComputedTail 3 =
      cutoffTwoMultiplicityTableSixLiteralTail 3 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_03
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_04

private theorem cutoffTwoMultiplicityTableSix_tail_02 :
    cutoffTwoMultiplicityTableSixComputedTail 2 =
      cutoffTwoMultiplicityTableSixLiteralTail 2 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_02
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_03

private theorem cutoffTwoMultiplicityTableSix_tail_01 :
    cutoffTwoMultiplicityTableSixComputedTail 1 =
      cutoffTwoMultiplicityTableSixLiteralTail 1 := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_01
  simpa [cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_02

theorem cutoffTwoMultiplicityTableSix_eq_literal :
    cutoffTwoMultiplicityTableSixComputed =
      cutoffTwoMultiplicityTableSixLiteral := by
  apply list_eq_of_take_eq_and_drop_eq cutoffTwoMultiplicityTableSixChunkSize
    cutoffTwoMultiplicityTableSix_chunk_00
  simpa [cutoffTwoMultiplicityTableSixComputed,
    cutoffTwoMultiplicityTableSixComputedTail,
    cutoffTwoMultiplicityTableSixLiteralTail,
    cutoffTwoMultiplicityTableSixChunkSize, List.drop_drop] using
      cutoffTwoMultiplicityTableSix_tail_01

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixCertificate.cutoffTwoMultiplicityTableSix_eq_literal
