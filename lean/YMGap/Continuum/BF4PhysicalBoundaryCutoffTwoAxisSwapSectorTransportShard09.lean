/-
Generated local-table certificates for axis-swap sector states
46 through 50.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09

set_option maxRecDepth 500000
set_option maxHeartbeats 500000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

theorem axisSwap01State46LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 46)
      (axisSwap01StateMatchedTargetFactors 55) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State46LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 46)
      (axisSwap01StateMatchedTargetFactors 55) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State46LinkTransportCheck

theorem axisSwap01State47LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 47)
      (axisSwap01StateMatchedTargetFactors 54) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State47LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 47)
      (axisSwap01StateMatchedTargetFactors 54) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State47LinkTransportCheck

theorem axisSwap01State48LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 48)
      (axisSwap01StateMatchedTargetFactors 56) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State48LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 48)
      (axisSwap01StateMatchedTargetFactors 56) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State48LinkTransportCheck

theorem axisSwap01State49LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 49)
      (axisSwap01StateMatchedTargetFactors 41) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State49LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 49)
      (axisSwap01StateMatchedTargetFactors 41) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State49LinkTransportCheck

theorem axisSwap01State50LinkTransportCheck :
    factorListTransportCheck 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01BoundaryRename
      (axisSwap01StateSourceFactors 50)
      (axisSwap01StateMatchedTargetFactors 43) = true := by
  unfold axisSwap01StateMatchedTargetFactors reorderFactorsWithLength
    axisSwap01StateSourceFactors cutoffTwoSectorStateAt
    axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01State50LinkTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename (axisSwap01StateSourceFactors 50)
      (axisSwap01StateMatchedTargetFactors 43) :=
  factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename _ _
    axisSwap01State50LinkTransportCheck

def axisSwap01Shard09Indices : List (Fin 65) :=
  [46, 47, 48, 49, 50]

theorem axisSwap01Shard09AllChecked :
    axisSwap01Shard09Indices.all
      axisSwap01StateLinkTransportCheckAt = true := by
  unfold axisSwap01Shard09Indices
    axisSwap01StateLinkTransportCheckAt
  change (factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 46)
        (axisSwap01StateMatchedTargetFactors 55) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 47)
        (axisSwap01StateMatchedTargetFactors 54) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 48)
        (axisSwap01StateMatchedTargetFactors 56) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 49)
        (axisSwap01StateMatchedTargetFactors 41) &&
      factorListTransportCheck 2 (centralFixedFaceIds 0)
        axisSwap01BoundaryRename axisSwap01BoundaryRename
        (axisSwap01StateSourceFactors 50)
        (axisSwap01StateMatchedTargetFactors 43) && true) = true
  rw [axisSwap01State46LinkTransportCheck, axisSwap01State47LinkTransportCheck, axisSwap01State48LinkTransportCheck, axisSwap01State49LinkTransportCheck, axisSwap01State50LinkTransportCheck]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09

#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State46LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State46LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State47LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State47LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State48LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State48LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State49LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State49LinkTransport
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State50LinkTransportCheck
#print axioms YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportShard09.axisSwap01State50LinkTransport
