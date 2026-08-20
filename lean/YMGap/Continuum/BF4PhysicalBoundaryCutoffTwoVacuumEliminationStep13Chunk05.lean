/- Independent widest-step checks for chunks 15 through 17. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_15 :
    ((step13Tail 15).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_16 :
    ((step13Tail 16).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_17 :
    ((step13Tail 17).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

