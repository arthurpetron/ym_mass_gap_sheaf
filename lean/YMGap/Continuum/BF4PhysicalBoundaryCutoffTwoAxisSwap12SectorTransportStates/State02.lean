/- Process-isolated second-axis-swap state 02. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12State02LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors 2)
      (axisSwap12StateMatchedTargetFactors 2) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State02LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt 2 = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors 2)
    (axisSwap12StateMatchedTargetFactors 2) = true
  exact axisSwap12State02LinkTransportCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12State02LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12State02LinkTransportCheckedAt
