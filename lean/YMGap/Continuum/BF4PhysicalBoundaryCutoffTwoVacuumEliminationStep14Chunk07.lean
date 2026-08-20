/- Independent step-14 checks for chunks 21 through 23. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_21 :
    ((step14Tail 21).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_22 :
    ((step14Tail 22).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_23 :
    ((step14Tail 23).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

