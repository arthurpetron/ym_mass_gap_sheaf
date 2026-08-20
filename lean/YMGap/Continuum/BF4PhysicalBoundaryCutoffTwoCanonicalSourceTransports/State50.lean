/- Checked canonical source-factor transport for state 50. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport50

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCommonTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalFactorPool
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorLocalZeroCertificate
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

def cutoffTwoCanonicalSourceTransport50Check : Bool :=
  factorListTransportCheck 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 50))
    (cutoffTwoCanonicalSourceFactorsAt 50)

theorem cutoffTwoCanonicalSourceTransport50Check_checked :
    cutoffTwoCanonicalSourceTransport50Check = true := by
  decide

theorem cutoffTwoCanonicalSourceTransport50 :
    FactorListTransport 2 (centralFixedFaceIds 0)
      cutoffTwoCanonicalIdentity
      (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 50))
      (cutoffTwoCanonicalSourceFactorsAt 50) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    cutoffTwoCanonicalIdentity cutoffTwoCanonicalIdentity
    (cutoffTwoSourceLinkFactors (cutoffTwoSectorLocalZeroStateAt 50))
    (cutoffTwoCanonicalSourceFactorsAt 50)
    cutoffTwoCanonicalSourceTransport50Check_checked

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport50

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalSourceTransport50.cutoffTwoCanonicalSourceTransport50
