/- Independent step-14 checks for chunks 3 through 5. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_03 :
    ((step14Tail 3).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_04 :
    ((step14Tail 4).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_05 :
    ((step14Tail 5).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

