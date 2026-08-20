/- Independent widest-step checks for chunks 72 through 74. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_72 :
    ((step13Tail 72).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_73 :
    ((step13Tail 73).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_74 :
    ((step13Tail 74).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

