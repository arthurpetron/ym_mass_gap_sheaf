/- Process-isolated second-axis-swap state 40. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12State40LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors 40)
      (axisSwap12StateMatchedTargetFactors 24) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State40LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt 40 = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors 40)
    (axisSwap12StateMatchedTargetFactors 24) = true
  exact axisSwap12State40LinkTransportCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12State40LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard07.axisSwap12State40LinkTransportCheckedAt
