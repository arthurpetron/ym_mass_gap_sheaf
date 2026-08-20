/- Independent widest-step checks for chunks 69 through 71. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_69 :
    ((step13Tail 69).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_70 :
    ((step13Tail 70).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_71 :
    ((step13Tail 71).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

