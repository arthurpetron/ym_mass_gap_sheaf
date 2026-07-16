/-
# Exact row certificates for the direct Base pieces

Pieces 2 and 4 contain no large squared sparse factor.  Their generated
coefficient rows are therefore reconciled directly with the staged raw
polynomials in one small certificate module.
-/

import YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

namespace YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open YMGap.Continuum.HarmonicLowerSixTailBaseSemanticRows
open YMGap.Continuum.RawGridSemanticTransport

theorem tailBaseStructuredPiece2Raw_bound :
    rawFirstExponentBound 23 tailBaseStructuredPiece2Raw = true := by
  rfl

theorem tailBaseStructuredPiece2Raw_rows :
    canonRowsRelationChunks 4 6
      (bucketRaw 23 tailBaseStructuredPiece2Raw)
      tailBaseSemanticPiece2Rows = true := by
  rfl

theorem tailBaseStructuredPiece4Raw_bound :
    rawFirstExponentBound 23 tailBaseStructuredPiece4Raw = true := by
  rfl

theorem tailBaseStructuredPiece4Raw_rows :
    canonRowsRelationChunks 4 6
      (bucketRaw 23 tailBaseStructuredPiece4Raw)
      tailBaseSemanticPiece4Rows = true := by
  rfl

#print axioms tailBaseStructuredPiece2Raw_rows
#print axioms tailBaseStructuredPiece4Raw_rows

end YMGap.Continuum.HarmonicLowerSixTailBaseSemanticBridge
