/- Independent step-15 check for chunk 3. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step15_chunk_03 :
    ((step15Tail 3).take step15ChunkSize).all step15Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep15
