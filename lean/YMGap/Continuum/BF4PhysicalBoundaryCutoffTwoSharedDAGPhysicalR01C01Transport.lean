/- Sharded physical-to-canonical factor-list transport for sector (1,1). -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Transport

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransportSharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01Sharded
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoPhysicalR01C01MatchedFactors : List ScopedQFactor :=
  (cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors) ++
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1) ++
      cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1))

def cutoffTwoCanonicalR01C01MatchedFactors : List ScopedQFactor :=
  cutoffTwoCanonicalCommonFactors ++
    (cutoffTwoCanonicalSourceFactorsAt 1 ++
      cutoffTwoCanonicalSourceFactorsAt 1)

theorem cutoffTwoPhysicalR01C01MatchedTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalTransportIdentity
      cutoffTwoPhysicalR01C01MatchedFactors
      cutoffTwoCanonicalR01C01MatchedFactors :=
  FactorListTransport.append
    cutoffTwoCanonicalCommonTransport
    (FactorListTransport.append
      cutoffTwoCanonicalSource01Transport
      cutoffTwoCanonicalSource01Transport)

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Transport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSharedDAGPhysicalR01C01Transport.cutoffTwoPhysicalR01C01MatchedTransport
