/- Independent step-14 checks for chunks 9 through 11. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_09 :
    ((step14Tail 9).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_10 :
    ((step14Tail 10).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_11 :
    ((step14Tail 11).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

