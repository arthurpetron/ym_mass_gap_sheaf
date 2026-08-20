/- Independent widest-step checks for chunks 36 through 38. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_36 :
    ((step13Tail 36).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_37 :
    ((step13Tail 37).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_38 :
    ((step13Tail 38).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

