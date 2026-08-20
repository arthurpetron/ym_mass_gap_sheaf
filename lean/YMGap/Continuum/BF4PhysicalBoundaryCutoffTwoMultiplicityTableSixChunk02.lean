/-
# Arity-six cutoff-two multiplicity table chunk 02

Kernel comparison of entries 162 through 242.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk02

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

theorem cutoffTwoMultiplicityTableSix_chunk_02 :
    (cutoffTwoMultiplicityTableSixComputedTail 2).take
        cutoffTwoMultiplicityTableSixChunkSize =
      (cutoffTwoMultiplicityTableSixLiteralTail 2).take
        cutoffTwoMultiplicityTableSixChunkSize := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk02

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk02.cutoffTwoMultiplicityTableSix_chunk_02
