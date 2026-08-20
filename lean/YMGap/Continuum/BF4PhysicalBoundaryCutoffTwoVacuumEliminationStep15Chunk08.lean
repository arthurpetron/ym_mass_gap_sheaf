/- Independent step-15 check for chunk 8. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step15_chunk_08 :
    ((step15Tail 8).take step15ChunkSize).all step15Predicate = true := by
  decide

theorem step15_tail_09_empty : step15Tail 9 = [] := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
