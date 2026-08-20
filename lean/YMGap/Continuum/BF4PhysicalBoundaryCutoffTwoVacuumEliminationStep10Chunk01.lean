/- Independent step-10 checks for chunks 3 through 5. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step10_chunk_03 :
    ((step10Tail 3).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_04 :
    ((step10Tail 4).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_05 :
    ((step10Tail 5).take step10ChunkSize).all step10Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

