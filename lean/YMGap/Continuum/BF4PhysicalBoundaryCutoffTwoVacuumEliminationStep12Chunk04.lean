/- Independent step-12 check for chunk 4. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step12_chunk_04 :
    ((step12Tail 4).take step12ChunkSize).all step12Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep12

