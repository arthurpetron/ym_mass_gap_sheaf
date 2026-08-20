/- Independent widest-step checks for chunks 60 through 62. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_60 :
    ((step13Tail 60).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_61 :
    ((step13Tail 61).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_62 :
    ((step13Tail 62).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

