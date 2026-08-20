/- Independent step-12 check for chunk 3. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step12_chunk_03 :
    ((step12Tail 3).take step12ChunkSize).all step12Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

