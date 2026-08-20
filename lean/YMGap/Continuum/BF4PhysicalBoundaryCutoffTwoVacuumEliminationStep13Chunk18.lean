/- Independent widest-step checks for chunks 54 through 56. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_54 :
    ((step13Tail 54).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_55 :
    ((step13Tail 55).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_56 :
    ((step13Tail 56).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

