/-
# Factorized exact rows for the old-slope square Base piece

The flat piece-3 normal form has 682 terms.  This module never constructs it
inside a closed equality check: it buckets the 201-term `U0Cleared^2` normal
form first, then applies every remaining D-only factor independently to each
N-exponent row.  The expensive row reconciliation is sealed here so semantic
consumers can reuse its olean without recomputing it.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.RawGridSemanticTransport

def tailBaseU0SquareRows : List RingNormaliser.RawPoly :=
  bucketRaw 23 tailBaseU0SquareRawPolynomial

def tailBasePiece3RowTransform
    (row : RingNormaliser.RawPoly) : RingNormaliser.RawPoly :=
  RingNormaliser.scaleTerm [0, 7] (-4)
    (RingNormaliser.canon
      (RingNormaliser.rawMul tailBaseDp15RawPolynomial
        (RingNormaliser.canon
          (RingNormaliser.rawMul tailBaseR4RawPolynomial row))))

def tailBasePiece3FactorRows : List RingNormaliser.RawPoly :=
  tailBaseU0SquareRows.map tailBasePiece3RowTransform

theorem tailBaseU0SquareRaw_bound :
    rawFirstExponentBound 23 tailBaseU0SquareRawPolynomial = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_0 :
    canonRowsRelation
      (tailBasePiece3FactorRows.take 4)
      (tailBaseSemanticPiece3Rows.take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_4 :
    canonRowsRelation
      ((tailBasePiece3FactorRows.drop 4).take 4)
      ((tailBaseSemanticPiece3Rows.drop 4).take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_8 :
    canonRowsRelation
      ((tailBasePiece3FactorRows.drop 8).take 4)
      ((tailBaseSemanticPiece3Rows.drop 8).take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_12 :
    canonRowsRelation
      ((tailBasePiece3FactorRows.drop 12).take 4)
      ((tailBaseSemanticPiece3Rows.drop 12).take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_16 :
    canonRowsRelation
      ((tailBasePiece3FactorRows.drop 16).take 4)
      ((tailBaseSemanticPiece3Rows.drop 16).take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_20 :
    canonRowsRelation
      ((tailBasePiece3FactorRows.drop 20).take 4)
      ((tailBaseSemanticPiece3Rows.drop 20).take 4) = true := by
  rfl

private theorem tailBasePiece3FactorRows_rows_24 :
    canonRowsRelation
      (tailBasePiece3FactorRows.drop 24)
      (tailBaseSemanticPiece3Rows.drop 24) = true := by
  rfl

/-- Exact reconciliation of the factorized row map with all 23 generated
piece-3 rows. -/
theorem tailBasePiece3FactorRows_rows :
    canonRowsRelationChunks 4 6
      tailBasePiece3FactorRows
      tailBaseSemanticPiece3Rows = true := by
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨tailBasePiece3FactorRows_rows_0, ?_⟩
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using
      tailBasePiece3FactorRows_rows_4
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using
      tailBasePiece3FactorRows_rows_8
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using
      tailBasePiece3FactorRows_rows_12
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using
      tailBasePiece3FactorRows_rows_16
  apply (Bool.and_eq_true _ _).mpr
  refine ⟨?_, ?_⟩
  · simpa only [List.drop_drop, Nat.add_comm] using
      tailBasePiece3FactorRows_rows_20
  simpa only [List.drop_drop, Nat.add_comm] using
    tailBasePiece3FactorRows_rows_24

#print axioms tailBaseU0SquareRaw_bound
#print axioms tailBasePiece3FactorRows_rows

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
