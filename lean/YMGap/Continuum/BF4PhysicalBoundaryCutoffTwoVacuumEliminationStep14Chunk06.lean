/- Independent step-14 checks for chunks 18 through 20. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_18 :
    ((step14Tail 18).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_19 :
    ((step14Tail 19).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_20 :
    ((step14Tail 20).take step14ChunkSize).all step14Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

