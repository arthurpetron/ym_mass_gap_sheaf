/- Independent step-14 checks for chunks 6 through 8. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_06 :
    ((step14Tail 6).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_07 :
    ((step14Tail 7).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_08 :
    ((step14Tail 8).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

