/- Independent step-10 checks for chunks 0 through 2. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step10_chunk_00 :
    ((step10Tail 0).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_01 :
    ((step10Tail 1).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_02 :
    ((step10Tail 2).take step10ChunkSize).all step10Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

