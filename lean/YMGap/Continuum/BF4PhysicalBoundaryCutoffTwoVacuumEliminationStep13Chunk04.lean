/- Independent widest-step checks for chunks 12 through 14. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_12 :
    ((step13Tail 12).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_13 :
    ((step13Tail 13).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_14 :
    ((step13Tail 14).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

