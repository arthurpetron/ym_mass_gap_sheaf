/- Independent step-10 checks for chunks 6 through 8. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step10_chunk_06 :
    ((step10Tail 6).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_07 :
    ((step10Tail 7).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_08 :
    ((step10Tail 8).take step10ChunkSize).all step10Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

