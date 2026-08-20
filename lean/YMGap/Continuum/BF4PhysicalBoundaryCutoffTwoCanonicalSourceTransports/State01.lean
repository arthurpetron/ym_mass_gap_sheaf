/- Checked canonical source-factor transport for state 1. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSourceTransport01Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1))
    (cutoffTwoCanonicalSourceFactorsAt 1)

theorem cutoffTwoCanonicalSourceTransport01Check_checked :
    cutoffTwoCanonicalSourceTransport01Check = true := by
  decide

theorem cutoffTwoCanonicalSourceTransport01 :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1))
      (cutoffTwoCanonicalSourceFactorsAt 1) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 1))
    (cutoffTwoCanonicalSourceFactorsAt 1)
    cutoffTwoCanonicalSourceTransport01Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport01.cutoffTwoCanonicalSourceTransport01
