/-
# Arity-six cutoff-two multiplicity table chunk 00

Kernel comparison of entries 0 through 80.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk00

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

theorem cutoffTwoMultiplicityTableSix_chunk_00 :
    (cutoffTwoMultiplicityTableSixComputedTail 0).take
        cutoffTwoMultiplicityTableSixChunkSize =
      (cutoffTwoMultiplicityTableSixLiteralTail 0).take
        cutoffTwoMultiplicityTableSixChunkSize := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk00

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk00.cutoffTwoMultiplicityTableSix_chunk_00
