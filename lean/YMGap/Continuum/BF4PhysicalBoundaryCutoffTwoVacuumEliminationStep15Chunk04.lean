/- Independent step-15 check for chunk 4. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step15_chunk_04 :
    ((step15Tail 4).take step15ChunkSize).all step15Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
