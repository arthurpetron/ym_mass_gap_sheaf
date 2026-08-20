/- Independent widest-step checks for chunks 21 through 23. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_21 :
    ((step13Tail 21).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_22 :
    ((step13Tail 22).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_23 :
    ((step13Tail 23).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

