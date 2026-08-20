/- Independent step-14 checks for chunks 12 through 14. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_12 :
    ((step14Tail 12).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_13 :
    ((step14Tail 13).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_14 :
    ((step14Tail 14).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

