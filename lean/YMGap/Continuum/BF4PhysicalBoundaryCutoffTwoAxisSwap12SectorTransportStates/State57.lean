/- Process-isolated second-axis-swap state 57. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12State57LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors 57)
      (axisSwap12StateMatchedTargetFactors 57) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State57LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt 57 = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors 57)
    (axisSwap12StateMatchedTargetFactors 57) = true
  exact axisSwap12State57LinkTransportCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12State57LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard11.axisSwap12State57LinkTransportCheckedAt
