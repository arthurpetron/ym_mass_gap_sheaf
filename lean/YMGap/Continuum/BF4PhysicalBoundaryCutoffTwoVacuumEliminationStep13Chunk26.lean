/- Independent widest-step checks for chunks 78 through 80. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_78 :
    ((step13Tail 78).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_79 :
    ((step13Tail 79).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_80 :
    ((step13Tail 80).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_tail_81_empty : step13Tail 81 = [] := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

