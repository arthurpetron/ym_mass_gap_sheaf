/- Independent widest-step checks for chunks 9 through 11. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_09 :
    ((step13Tail 9).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_10 :
    ((step13Tail 10).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_11 :
    ((step13Tail 11).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

