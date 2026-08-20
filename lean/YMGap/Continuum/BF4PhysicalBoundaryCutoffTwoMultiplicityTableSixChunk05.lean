/-
# Arity-six cutoff-two multiplicity table chunk 05

Kernel comparison of entries 405 through 485.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk05

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

theorem cutoffTwoMultiplicityTableSix_chunk_05 :
    (cutoffTwoMultiplicityTableSixComputedTail 5).take
        cutoffTwoMultiplicityTableSixChunkSize =
      (cutoffTwoMultiplicityTableSixLiteralTail 5).take
        cutoffTwoMultiplicityTableSixChunkSize := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk05

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk05.cutoffTwoMultiplicityTableSix_chunk_05
