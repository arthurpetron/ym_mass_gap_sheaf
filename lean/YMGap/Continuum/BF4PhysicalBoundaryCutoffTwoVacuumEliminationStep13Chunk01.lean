/- Independent widest-step checks for chunks 3 through 5. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_03 :
    ((step13Tail 3).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_04 :
    ((step13Tail 4).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_05 :
    ((step13Tail 5).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

