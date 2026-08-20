/- Independent widest-step checks for chunks 45 through 47. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_45 :
    ((step13Tail 45).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_46 :
    ((step13Tail 46).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_47 :
    ((step13Tail 47).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

