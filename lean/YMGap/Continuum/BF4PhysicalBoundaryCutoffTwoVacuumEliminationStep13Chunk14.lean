/- Independent widest-step checks for chunks 42 through 44. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_42 :
    ((step13Tail 42).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_43 :
    ((step13Tail 43).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_44 :
    ((step13Tail 44).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

