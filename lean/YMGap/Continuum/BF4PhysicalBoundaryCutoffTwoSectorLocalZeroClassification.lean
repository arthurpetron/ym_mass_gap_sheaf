/-
# Complete local classification of the zero entries in the 65-sector block

Each raw-table zero carries a kernel-checked one-coordinate source-factor
incompatibility witness.  The final theorem turns that local witness into a
zero of the genuine finite physical reflected kernel.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk00
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk01
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk02
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk03
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk04
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk05
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk06
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk07
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk08
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk09
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk10
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk11
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroAggregateChunks.Chunk12

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorRawKernelCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem listAll_append_true {A : Type} {predicate : A → Bool}
    {left right : List A}
    (hleft : left.all predicate = true)
    (hright : right.all predicate = true) :
    (left ++ right).all predicate = true := by
  rw [List.all_append, hleft, hright]
  rfl

theorem cutoffTwoSectorLocalZeroRows_checked
    (row : Nat) (hrow : row < 65) :
    cutoffTwoSectorLocalZeroRowCheck row = true := by
  have hcombined :
      ([0, 1, 2, 3, 4] ++ [5, 6, 7, 8, 9] ++ [10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]).all cutoffTwoSectorLocalZeroRowCheck = true :=
    listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [0, 1, 2, 3, 4]) (right := [5, 6, 7, 8, 9] ++ [10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk00_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [5, 6, 7, 8, 9]) (right := [10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk01_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [10, 11, 12, 13, 14]) (right := [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk02_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [15, 16, 17, 18, 19]) (right := [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk03_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [20, 21, 22, 23, 24]) (right := [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk04_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [25, 26, 27, 28, 29]) (right := [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk05_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [30, 31, 32, 33, 34]) (right := [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk06_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [35, 36, 37, 38, 39]) (right := [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk07_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [40, 41, 42, 43, 44]) (right := [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk08_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [45, 46, 47, 48, 49]) (right := [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk09_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [50, 51, 52, 53, 54]) (right := [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk10_checked (listAll_append_true (predicate := cutoffTwoSectorLocalZeroRowCheck) (left := [55, 56, 57, 58, 59]) (right := [60, 61, 62, 63, 64]) cutoffTwoSectorLocalZeroRowsChunk11_checked (cutoffTwoSectorLocalZeroRowsChunk12_checked))))))))))))
  have hsplit : List.range 65 = [0, 1, 2, 3, 4] ++ [5, 6, 7, 8, 9] ++ [10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64] := by
    decide
  have htransport :
      (([0, 1, 2, 3, 4] ++ [5, 6, 7, 8, 9] ++ [10, 11, 12, 13, 14] ++ [15, 16, 17, 18, 19] ++ [20, 21, 22, 23, 24] ++ [25, 26, 27, 28, 29] ++ [30, 31, 32, 33, 34] ++ [35, 36, 37, 38, 39] ++ [40, 41, 42, 43, 44] ++ [45, 46, 47, 48, 49] ++ [50, 51, 52, 53, 54] ++ [55, 56, 57, 58, 59] ++ [60, 61, 62, 63, 64]).all cutoffTwoSectorLocalZeroRowCheck = true) =
        ((List.range 65).all cutoffTwoSectorLocalZeroRowCheck = true) :=
    congrArg
      (fun rows => rows.all cutoffTwoSectorLocalZeroRowCheck = true)
      hsplit.symm
  have hall :
      (List.range 65).all cutoffTwoSectorLocalZeroRowCheck = true := by
    exact Eq.mp htransport hcombined
  exact List.all_eq_true.mp hall row (List.mem_range.mpr hrow)

theorem cutoffTwoSectorLocalZeroWitness_of_raw_eqv_zero
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65)
    (hzero : cutoffTwoSectorRawKernel row column ≈ 0) :
    cutoffTwoSectorLocalZeroWitness row column ∈
        YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.centralFixedFaceIds 0 ∧
      cutoffTwoSectorIndexPairLocalZeroAtCheck row column
        (cutoffTwoSectorLocalZeroWitness row column) = true :=
  cutoffTwoSectorLocalZeroRowCheck_sound
    (cutoffTwoSectorLocalZeroRows_checked row hrow) hcolumn hzero

theorem centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw
    {row column : Nat} (hrow : row < 65) (hcolumn : column < 65)
    (hzero : cutoffTwoSectorRawKernel row column ≈ 0) :
    centralPhysicalReflectedKernel cutoffTwoHalfCoupling 2 0
      (cutoffTwoSectorLocalZeroStateAt row)
      (cutoffTwoSectorLocalZeroStateAt column) ≈ 0 := by
  have hwitness := cutoffTwoSectorLocalZeroWitness_of_raw_eqv_zero
    hrow hcolumn hzero
  exact
    centralPhysicalReflectedKernel_cutoffTwo_sector_eqv_zero_of_local_at_check
      (cutoffTwoSectorLocalZeroStateAt row)
      (cutoffTwoSectorLocalZeroStateAt column)
      (cutoffTwoSectorLocalZeroWitness row column)
      (cutoffTwoSectorLocalZeroStateAt_mem hrow)
      (cutoffTwoSectorLocalZeroStateAt_mem hcolumn)
      hwitness.1 hwitness.2

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.cutoffTwoSectorLocalZeroWitness_of_raw_eqv_zero
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroClassification.centralPhysicalReflectedKernel_cutoffTwo_sector_index_eqv_zero_of_raw
