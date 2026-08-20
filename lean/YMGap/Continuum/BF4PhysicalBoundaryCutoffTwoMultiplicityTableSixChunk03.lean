/-
# Arity-six cutoff-two multiplicity table chunk 03

Kernel comparison of entries 243 through 323.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk03

set_option maxRecDepth 300000
set_option maxHeartbeats 20000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSix

theorem cutoffTwoMultiplicityTableSix_chunk_03 :
    (cutoffTwoMultiplicityTableSixComputedTail 3).take
        cutoffTwoMultiplicityTableSixChunkSize =
      (cutoffTwoMultiplicityTableSixLiteralTail 3).take
        cutoffTwoMultiplicityTableSixChunkSize := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk03

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoMultiplicityTableSixChunk03.cutoffTwoMultiplicityTableSix_chunk_03
