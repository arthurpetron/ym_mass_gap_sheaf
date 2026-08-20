/- Independent widest-step checks for chunks 0 through 2. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_00 :
    ((step13Tail 0).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_01 :
    ((step13Tail 1).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_02 :
    ((step13Tail 2).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

