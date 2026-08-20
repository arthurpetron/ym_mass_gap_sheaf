/- Exact terminal scalar for the shared-DAG trace (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Terminal

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSharedDAGTraceR01C01Terminal_eqv_one :
    scopedFactorPartitionSum 2
        (cutoffTwoCubeInterfaceEliminationOrder.drop 24)
        cutoffTwoSharedDAGTraceR01C01Factors24 ≈ (1 : Q') := by
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Terminal

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Terminal.cutoffTwoSharedDAGTraceR01C01Terminal_eqv_one
