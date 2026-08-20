/- Lift the checked factor-list transport for (1,1) to its partition sum. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01PartitionTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 50000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Certificate
open YMGap.Continuum.FiniteScopedFactorDAGCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate.CheckedScopedEliminationStep
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

theorem cutoffTwoPhysicalR01C01MatchedPartitionSum_eqv :
    scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoPhysicalR01C01MatchedFactors ≈
      scopedFactorPartitionSum 2 (centralFixedFaceIds 0)
        cutoffTwoCanonicalR01C01MatchedFactors := by
  simpa [cutoffTwoCanonicalTransportIdentity] using
    scopedFactorPartitionSum_eqv_of_identity_listTransport 2
      (centralFixedFaceIds 0)
      cutoffTwoPhysicalR01C01MatchedTransport

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01PartitionTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01PartitionTransport.cutoffTwoPhysicalR01C01MatchedPartitionSum_eqv
