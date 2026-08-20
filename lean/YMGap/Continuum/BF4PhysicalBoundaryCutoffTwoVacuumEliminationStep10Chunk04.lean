/- Independent step-10 checks for chunks 12 through 14. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step10_chunk_12 :
    ((step10Tail 12).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_13 :
    ((step10Tail 13).take step10ChunkSize).all step10Predicate = true := by
  decide

theorem step10_chunk_14 :
    ((step10Tail 14).take step10ChunkSize).all step10Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep10

