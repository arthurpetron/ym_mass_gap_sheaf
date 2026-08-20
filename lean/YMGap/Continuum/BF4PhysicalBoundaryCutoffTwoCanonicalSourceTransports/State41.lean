/- Checked canonical source-factor transport for state 41. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport41

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSourceTransport41Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 41))
    (cutoffTwoCanonicalSourceFactorsAt 41)

theorem cutoffTwoCanonicalSourceTransport41Check_checked :
    cutoffTwoCanonicalSourceTransport41Check = true := by
  decide

theorem cutoffTwoCanonicalSourceTransport41 :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 41))
      (cutoffTwoCanonicalSourceFactorsAt 41) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 41))
    (cutoffTwoCanonicalSourceFactorsAt 41)
    cutoffTwoCanonicalSourceTransport41Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport41

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport41.cutoffTwoCanonicalSourceTransport41
