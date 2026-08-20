/-
# Shared finite data for axis-swap sector transports

This module packages the exact 65-state action and the reusable 48-factor
target reordering.  Later shards check the production local tables for each
state independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

def cutoffTwoSectorStateAt (index : Fin 65) : EdgeLabelling :=
  cutoffTwoCubeSectorStates.get
    (Fin.cast cutoffTwoCubeSectorStates_length.symm index)

def axisSwap01StateSourceFactors
    (index : Fin 65) : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors (cutoffTwoSectorStateAt index)

theorem axisSwap01StateSourceFactor_count (index : Fin 65) :
    (axisSwap01StateSourceFactors index).length = 48 := by
  unfold axisSwap01StateSourceFactors cutoffTwoSourceLinkFactors
  simp only [List.length_map]
  decide

def axisSwap01StateMatchedTargetFactors
    (targetIndex : Fin 65) : List ScopedQFactor :=
  reorderFactorsWithLength (axisSwap01StateSourceFactors targetIndex) 48
    (axisSwap01StateSourceFactor_count targetIndex)
    axisSwap01LowerLinkTargetOrder

theorem axisSwap01StateMatchedTargetFactors_perm
    (targetIndex : Fin 65) :
    (axisSwap01StateMatchedTargetFactors targetIndex).Perm
      (axisSwap01StateSourceFactors targetIndex) :=
  reorderFactorsWithLength_perm
    (axisSwap01StateSourceFactors targetIndex) 48
    (axisSwap01StateSourceFactor_count targetIndex)
    axisSwap01LowerLinkTargetOrder axisSwap01LowerLinkTargetOrder_perm

/-- The exact action on the sector order: cube first, then binary masks. -/
def axisSwap01SectorTargetOrder : List (Fin 65) :=
  [0, 1, 3, 2, 4, 5, 7, 6, 8, 17, 19, 18, 20,
   21, 23, 22, 24, 9, 11, 10, 12, 13, 15, 14, 16,
   25, 27, 26, 28, 29, 31, 30, 32, 33, 35, 34, 36,
   37, 39, 38, 40, 49, 51, 50, 52, 53, 55, 54, 56,
   41, 43, 42, 44, 45, 47, 46, 48, 57, 59, 58, 60,
   61, 63, 62, 64]

theorem axisSwap01SectorTargetOrder_length :
    axisSwap01SectorTargetOrder.length = 65 := by
  rfl

def axisSwap01SectorTargetIndex (sourceIndex : Fin 65) : Fin 65 :=
  axisSwap01SectorTargetOrder.get
    (Fin.cast axisSwap01SectorTargetOrder_length.symm sourceIndex)

def axisSwap01StateLinkTransportCheckAt (sourceIndex : Fin 65) : Bool :=
  factorListTransportCheck 2
    (YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.centralFixedFaceIds 0)
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport.axisSwap01BoundaryRename
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport.axisSwap01BoundaryRename
    (axisSwap01StateSourceFactors sourceIndex)
    (axisSwap01StateMatchedTargetFactors
      (axisSwap01SectorTargetIndex sourceIndex))

theorem axisSwap01SectorTargetOrder_perm :
    axisSwap01SectorTargetOrder.Perm (List.finRange 65) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap01SectorTargetOrder
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData.axisSwap01StateMatchedTargetFactors_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapSectorTransportData.axisSwap01SectorTargetOrder_perm
