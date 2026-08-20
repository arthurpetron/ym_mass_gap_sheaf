/- Independent step-14 checks for chunks 0 through 2. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_00 :
    ((step14Tail 0).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_01 :
    ((step14Tail 1).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_02 :
    ((step14Tail 2).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

