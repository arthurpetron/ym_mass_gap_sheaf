/- Canonical interface value for sector pair (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Composition
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Terminal

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Composition
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Terminal
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoSharedDAGTraceR01C01Ordered_eqv_one :
    scopedFactorPartitionSum 2 cutoffTwoCubeInterfaceEliminationOrder
        cutoffTwoSharedDAGTraceR01C01Factors0 ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _
    cutoffTwoSharedDAGTraceR01C01Segments_partitionSum_eqv
    cutoffTwoSharedDAGTraceR01C01Terminal_eqv_one

theorem cutoffTwoSharedDAGTraceR01C01Interface_eqv_one :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR01C01Factors0 ≈ (1 : Q') := by
  unfold scopedFactorPartitionSum
  exact Q'.eqv_trans _ _ _
    (listQSum_bounded_perm 2
      (scopedFactorProduct cutoffTwoSharedDAGTraceR01C01Factors0)
      cutoffTwoCubeInterfaceEliminationOrder_perm.symm)
    cutoffTwoSharedDAGTraceR01C01Ordered_eqv_one

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate.cutoffTwoSharedDAGTraceR01C01Interface_eqv_one
