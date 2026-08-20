/- Independent widest-step checks for chunks 66 through 68. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_66 :
    ((step13Tail 66).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_67 :
    ((step13Tail 67).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_68 :
    ((step13Tail 68).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

