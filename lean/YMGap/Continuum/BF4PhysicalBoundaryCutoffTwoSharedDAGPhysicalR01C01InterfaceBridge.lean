/- Genuine physical interface sum equals the checked canonical value for (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01PartitionTransport
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01InterfaceBridge

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01PartitionTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01Data
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGTraceR01C01InterfaceCertificate
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoPhysicalR01C01Factors_eq_matched :
    cutoffTwoSectorPairInterfaceFactors
        (cutoffTwoSectorLocalZeroStateAt 1)
        (cutoffTwoSectorLocalZeroStateAt 1) =
      cutoffTwoPhysicalR01C01MatchedFactors := by
  simp [cutoffTwoSectorPairInterfaceFactors,
    cutoffTwoPhysicalR01C01MatchedFactors, List.append_assoc]

theorem cutoffTwoPhysicalR01C01Interface_eqv_canonical :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 1)) ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoSharedDAGTraceR01C01Factors0 := by
  rw [cutoffTwoPhysicalR01C01Factors_eq_matched]
  exact Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR01C01MatchedPartitionSum_eqv
    (scopedFactorPartitionSum_perm 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalR01C01Matched_perm_trace)

theorem cutoffTwoPhysicalR01C01Interface_eqv_one :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        (cutoffTwoSectorPairInterfaceFactors
          (cutoffTwoSectorLocalZeroStateAt 1)
          (cutoffTwoSectorLocalZeroStateAt 1)) ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _
    cutoffTwoPhysicalR01C01Interface_eqv_canonical
    cutoffTwoSharedDAGTraceR01C01Interface_eqv_one

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01InterfaceBridge

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01InterfaceBridge.cutoffTwoPhysicalR01C01Interface_eqv_one
