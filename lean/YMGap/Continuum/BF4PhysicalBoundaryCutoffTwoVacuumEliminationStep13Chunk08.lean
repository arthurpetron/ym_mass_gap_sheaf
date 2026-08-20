/- Independent widest-step checks for chunks 24 through 26. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_24 :
    ((step13Tail 24).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_25 :
    ((step13Tail 25).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_26 :
    ((step13Tail 26).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

