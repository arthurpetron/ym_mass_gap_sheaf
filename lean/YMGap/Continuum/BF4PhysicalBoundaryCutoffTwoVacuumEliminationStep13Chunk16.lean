/- Independent widest-step checks for chunks 48 through 50. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_48 :
    ((step13Tail 48).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_49 :
    ((step13Tail 49).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_50 :
    ((step13Tail 50).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

