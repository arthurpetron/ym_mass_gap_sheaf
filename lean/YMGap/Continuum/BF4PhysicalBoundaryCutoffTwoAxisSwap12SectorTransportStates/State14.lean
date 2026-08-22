/- Process-isolated second-axis-swap state 14. -/
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap12State14LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors 14)
      (axisSwap12StateMatchedTargetFactors 12) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State14LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt 14 = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors 14)
    (axisSwap12StateMatchedTargetFactors 12) = true
  exact axisSwap12State14LinkTransportCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12State14LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard02.axisSwap12State14LinkTransportCheckedAt
