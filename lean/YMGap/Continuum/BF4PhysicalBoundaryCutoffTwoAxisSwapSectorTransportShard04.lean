/-
Generated local-table certificates for axis-swap sector states
21 through 25.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State21LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 21)
      (axisSwap01StateMatchedTargetFactors 13) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State21LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 21)
      (axisSwap01StateMatchedTargetFactors 13) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State21LinkTransportCheck

theorem axisSwap01State22LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 22)
      (axisSwap01StateMatchedTargetFactors 15) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State22LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 22)
      (axisSwap01StateMatchedTargetFactors 15) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State22LinkTransportCheck

theorem axisSwap01State23LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 23)
      (axisSwap01StateMatchedTargetFactors 14) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State23LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 23)
      (axisSwap01StateMatchedTargetFactors 14) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State23LinkTransportCheck

theorem axisSwap01State24LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 24)
      (axisSwap01StateMatchedTargetFactors 16) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State24LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 24)
      (axisSwap01StateMatchedTargetFactors 16) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State24LinkTransportCheck

theorem axisSwap01State25LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 25)
      (axisSwap01StateMatchedTargetFactors 25) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State25LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 25)
      (axisSwap01StateMatchedTargetFactors 25) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State25LinkTransportCheck

def axisSwap01Shard04Indices : List (Fin 65) :=
  [21, 22, 23, 24, 25]

theorem axisSwap01Shard04AllChecked :
    axisSwap01Shard04Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard04Indices
    axisSwap01StateLinkTransportCheckAt
  change (factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 21)
        (axisSwap01StateMatchedTargetFactors 13) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 22)
        (axisSwap01StateMatchedTargetFactors 15) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 23)
        (axisSwap01StateMatchedTargetFactors 14) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 24)
        (axisSwap01StateMatchedTargetFactors 16) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 25)
        (axisSwap01StateMatchedTargetFactors 25) && true) = true
  rw [axisSwap01State21LinkTransportCheck, axisSwap01State22LinkTransportCheck, axisSwap01State23LinkTransportCheck, axisSwap01State24LinkTransportCheck, axisSwap01State25LinkTransportCheck]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State21LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State21LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State22LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State22LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State23LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State23LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State24LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State24LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State25LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard04.axisSwap01State25LinkTransport
