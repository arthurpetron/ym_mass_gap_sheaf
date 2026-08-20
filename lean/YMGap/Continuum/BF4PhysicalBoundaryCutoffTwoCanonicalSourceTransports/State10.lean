/- Checked canonical source-factor transport for state 10. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport10

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSourceTransport10Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 10))
    (cutoffTwoCanonicalSourceFactorsAt 10)

theorem cutoffTwoCanonicalSourceTransport10Check_checked :
    cutoffTwoCanonicalSourceTransport10Check = true := by
  decide

theorem cutoffTwoCanonicalSourceTransport10 :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 10))
      (cutoffTwoCanonicalSourceFactorsAt 10) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 10))
    (cutoffTwoCanonicalSourceFactorsAt 10)
    cutoffTwoCanonicalSourceTransport10Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport10

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport10.cutoffTwoCanonicalSourceTransport10
