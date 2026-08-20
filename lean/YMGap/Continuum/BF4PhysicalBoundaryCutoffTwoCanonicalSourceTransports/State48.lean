/- Checked canonical source-factor transport for state 48. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport48

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSourceTransport48Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 48))
    (cutoffTwoCanonicalSourceFactorsAt 48)

theorem cutoffTwoCanonicalSourceTransport48Check_checked :
    cutoffTwoCanonicalSourceTransport48Check = true := by
  decide

theorem cutoffTwoCanonicalSourceTransport48 :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 48))
      (cutoffTwoCanonicalSourceFactorsAt 48) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 48))
    (cutoffTwoCanonicalSourceFactorsAt 48)
    cutoffTwoCanonicalSourceTransport48Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport48

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport48.cutoffTwoCanonicalSourceTransport48
