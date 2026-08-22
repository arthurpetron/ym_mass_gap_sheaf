/- Process-isolated second-axis-swap state 01. -/
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

theorem axisSwap12State01LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12BoundaryRename
      (axisSwap12StateSourceFactors 1)
      (axisSwap12StateMatchedTargetFactors 1) = true := by
  unfold axisSwap12StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap12StateSourceFactors cutoffTwoSectorStateAt
    axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12State01LinkTransportCheckedAt :
    axisSwap12StateLinkTransportCheckAt 1 = true := by
  change factorListTransportCheck 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors 1)
    (axisSwap12StateMatchedTargetFactors 1) = true
  exact axisSwap12State01LinkTransportCheck

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12State01LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportShard00.axisSwap12State01LinkTransportCheckedAt
