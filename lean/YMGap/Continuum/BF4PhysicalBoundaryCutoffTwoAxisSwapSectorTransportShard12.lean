/-
Generated local-table certificates for axis-swap sector states
61 through 64.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State61LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 61)
      (axisSwap01StateMatchedTargetFactors 61) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State61LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 61)
      (axisSwap01StateMatchedTargetFactors 61) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State61LinkTransportCheck

theorem axisSwap01State62LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 62)
      (axisSwap01StateMatchedTargetFactors 63) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State62LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 62)
      (axisSwap01StateMatchedTargetFactors 63) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State62LinkTransportCheck

theorem axisSwap01State63LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 63)
      (axisSwap01StateMatchedTargetFactors 62) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State63LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 63)
      (axisSwap01StateMatchedTargetFactors 62) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State63LinkTransportCheck

theorem axisSwap01State64LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 64)
      (axisSwap01StateMatchedTargetFactors 64) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State64LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 64)
      (axisSwap01StateMatchedTargetFactors 64) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State64LinkTransportCheck

def axisSwap01Shard12Indices : List (Fin 65) :=
  [61, 62, 63, 64]

theorem axisSwap01Shard12AllChecked :
    axisSwap01Shard12Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard12Indices
    axisSwap01StateLinkTransportCheckAt
  change (factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 61)
        (axisSwap01StateMatchedTargetFactors 61) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 62)
        (axisSwap01StateMatchedTargetFactors 63) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 63)
        (axisSwap01StateMatchedTargetFactors 62) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 64)
        (axisSwap01StateMatchedTargetFactors 64) && true) = true
  rw [axisSwap01State61LinkTransportCheck, axisSwap01State62LinkTransportCheck, axisSwap01State63LinkTransportCheck, axisSwap01State64LinkTransportCheck]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State61LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State61LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State62LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State62LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State63LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State63LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State64LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard12.axisSwap01State64LinkTransport
