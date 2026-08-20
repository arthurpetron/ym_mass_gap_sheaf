/- Independent widest-step checks for chunks 33 through 35. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_33 :
    ((step13Tail 33).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_34 :
    ((step13Tail 34).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_35 :
    ((step13Tail 35).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

