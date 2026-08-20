/- Independent step-14 checks for chunks 15 through 17. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_15 :
    ((step14Tail 15).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_16 :
    ((step14Tail 16).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_17 :
    ((step14Tail 17).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

