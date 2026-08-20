/- Independent step-12 check for chunk 1. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step12_chunk_01 :
    ((step12Tail 1).take step12ChunkSize).all step12Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

