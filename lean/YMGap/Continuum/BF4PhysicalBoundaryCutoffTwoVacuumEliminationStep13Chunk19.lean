/- Independent widest-step checks for chunks 57 through 59. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_57 :
    ((step13Tail 57).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_58 :
    ((step13Tail 58).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_59 :
    ((step13Tail 59).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

