/- Independent widest-step checks for chunks 63 through 65. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step13_chunk_63 :
    ((step13Tail 63).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_64 :
    ((step13Tail 64).take step13ChunkSize).all step13Predicate = true := by
  decide

theorem step13_chunk_65 :
    ((step13Tail 65).take step13ChunkSize).all step13Predicate = true := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep13

