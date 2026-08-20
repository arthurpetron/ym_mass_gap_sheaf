/- Independent widest-step checks for chunks 51 through 53. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_51 :
    ((step13Tail 51).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_52 :
    ((step13Tail 52).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_53 :
    ((step13Tail 53).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

