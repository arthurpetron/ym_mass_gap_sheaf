/-
Generated local-table certificates for axis-swap sector states
16 through 20.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State16LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 16)
      (axisSwap01StateMatchedTargetFactors 24) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State16LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 16)
      (axisSwap01StateMatchedTargetFactors 24) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State16LinkTransportCheck

theorem axisSwap01State17LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 17)
      (axisSwap01StateMatchedTargetFactors 9) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State17LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 17)
      (axisSwap01StateMatchedTargetFactors 9) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State17LinkTransportCheck

theorem axisSwap01State18LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 18)
      (axisSwap01StateMatchedTargetFactors 11) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State18LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 18)
      (axisSwap01StateMatchedTargetFactors 11) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State18LinkTransportCheck

theorem axisSwap01State19LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 19)
      (axisSwap01StateMatchedTargetFactors 10) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State19LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 19)
      (axisSwap01StateMatchedTargetFactors 10) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State19LinkTransportCheck

theorem axisSwap01State20LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 20)
      (axisSwap01StateMatchedTargetFactors 12) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State20LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 20)
      (axisSwap01StateMatchedTargetFactors 12) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State20LinkTransportCheck

def axisSwap01Shard03Indices : List (Fin 65) :=
  [16, 17, 18, 19, 20]

theorem axisSwap01Shard03AllChecked :
    axisSwap01Shard03Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard03Indices
    axisSwap01StateLinkTransportCheckAt
  change (factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 16)
        (axisSwap01StateMatchedTargetFactors 24) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 17)
        (axisSwap01StateMatchedTargetFactors 9) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 18)
        (axisSwap01StateMatchedTargetFactors 11) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 19)
        (axisSwap01StateMatchedTargetFactors 10) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 20)
        (axisSwap01StateMatchedTargetFactors 12) && true) = true
  rw [axisSwap01State16LinkTransportCheck, axisSwap01State17LinkTransportCheck, axisSwap01State18LinkTransportCheck, axisSwap01State19LinkTransportCheck, axisSwap01State20LinkTransportCheck]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State16LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State16LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State17LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State17LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State18LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State18LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State19LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State19LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State20LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard03.axisSwap01State20LinkTransport
