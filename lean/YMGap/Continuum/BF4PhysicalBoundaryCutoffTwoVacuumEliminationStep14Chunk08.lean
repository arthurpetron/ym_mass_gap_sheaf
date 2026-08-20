/- Independent step-14 checks for chunks 24 through 26. -/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14Base

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

set_option maxRecDepth 1000000
set_option maxHeartbeats 50000000

theorem step14_chunk_24 :
    ((step14Tail 24).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_25 :
    ((step14Tail 25).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_chunk_26 :
    ((step14Tail 26).take step14ChunkSize).all step14Predicate = true := by
  decide

theorem step14_tail_27_empty : step14Tail 27 = [] := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumEliminationStep14

