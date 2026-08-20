/-
# Arity-six cutoff-two multiplicity table chunk 06

Kernel comparison of entries 486 through 566.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk06

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

theorem cutoffTwoMultiplicityTableSix_chunk_06 :
    (cutoffTwoMultiplicityTableSixComputedTail 6).take
        cutoffTwoMultiplicityTableSixChunkSize =
      (cutoffTwoMultiplicityTableSixLiteralTail 6).take
        cutoffTwoMultiplicityTableSixChunkSize := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk06

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk06.cutoffTwoMultiplicityTableSix_chunk_06
