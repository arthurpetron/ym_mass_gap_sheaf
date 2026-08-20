/-
Generated local-table certificates for axis-swap sector states
31 through 35.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State31LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 31)
      (axisSwap01StateMatchedTargetFactors 30) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State31LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 31)
      (axisSwap01StateMatchedTargetFactors 30) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State31LinkTransportCheck

theorem axisSwap01State32LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 32)
      (axisSwap01StateMatchedTargetFactors 32) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State32LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 32)
      (axisSwap01StateMatchedTargetFactors 32) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State32LinkTransportCheck

theorem axisSwap01State33LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 33)
      (axisSwap01StateMatchedTargetFactors 33) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State33LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 33)
      (axisSwap01StateMatchedTargetFactors 33) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State33LinkTransportCheck

theorem axisSwap01State34LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 34)
      (axisSwap01StateMatchedTargetFactors 35) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State34LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 34)
      (axisSwap01StateMatchedTargetFactors 35) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State34LinkTransportCheck

theorem axisSwap01State35LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 35)
      (axisSwap01StateMatchedTargetFactors 34) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State35LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 35)
      (axisSwap01StateMatchedTargetFactors 34) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State35LinkTransportCheck

def axisSwap01Shard06Indices : List (Fin 65) :=
  [31, 32, 33, 34, 35]

theorem axisSwap01Shard06AllChecked :
    axisSwap01Shard06Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard06Indices
    axisSwap01StateLinkTransportCheckAt
  change (factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 31)
        (axisSwap01StateMatchedTargetFactors 30) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 32)
        (axisSwap01StateMatchedTargetFactors 32) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 33)
        (axisSwap01StateMatchedTargetFactors 33) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 34)
        (axisSwap01StateMatchedTargetFactors 35) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 35)
        (axisSwap01StateMatchedTargetFactors 34) && true) = true
  rw [axisSwap01State31LinkTransportCheck, axisSwap01State32LinkTransportCheck, axisSwap01State33LinkTransportCheck, axisSwap01State34LinkTransportCheck, axisSwap01State35LinkTransportCheck]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State31LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State31LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State32LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State32LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State33LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State33LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State34LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State34LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State35LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard06.axisSwap01State35LinkTransport
