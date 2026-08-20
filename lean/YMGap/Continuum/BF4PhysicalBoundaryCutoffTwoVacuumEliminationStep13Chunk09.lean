/- Independent widest-step checks for chunks 27 through 29. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_27 :
    ((step13Tail 27).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_28 :
    ((step13Tail 28).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_29 :
    ((step13Tail 29).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

