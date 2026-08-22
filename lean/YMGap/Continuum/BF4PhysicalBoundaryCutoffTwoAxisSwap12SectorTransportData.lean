/-
# Shared finite data for axis-swap sector transports

This module packages the exact 65-state action and the reusable 48-factor
target reordering.  Later shards check the production local tables for each
state independently.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

def cutoffTwoSectorStateAt (index : Fin 65) : EdgeLabelling :=
  cutoffTwoCubeSectorStates.get
    (Fin.cast cutoffTwoCubeSectorStates_length.symm index)

def axisSwap12StateSourceFactors
    (index : Fin 65) : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors (cutoffTwoSectorStateAt index)

theorem axisSwap12StateSourceFactor_count (index : Fin 65) :
    (axisSwap12StateSourceFactors index).length = 48 := by
  unfold axisSwap12StateSourceFactors cutoffTwoSourceLinkFactors
  simp only [List.length_map]
  decide

def axisSwap12StateMatchedTargetFactors
    (targetIndex : Fin 65) : List ScopedQFactor :=
  reorderFactorsWithLength (axisSwap12StateSourceFactors targetIndex) 48
    (axisSwap12StateSourceFactor_count targetIndex)
    axisSwap12LowerLinkTargetOrder

theorem axisSwap12StateMatchedTargetFactors_perm
    (targetIndex : Fin 65) :
    (axisSwap12StateMatchedTargetFactors targetIndex).Perm
      (axisSwap12StateSourceFactors targetIndex) :=
  reorderFactorsWithLength_perm
    (axisSwap12StateSourceFactors targetIndex) 48
    (axisSwap12StateSourceFactor_count targetIndex)
    axisSwap12LowerLinkTargetOrder axisSwap12LowerLinkTargetOrder_perm

/-- The exact action on the sector order: cube first, then binary masks. -/
def axisSwap12SectorTargetOrder : List (Fin 65) :=
  [0, 1, 2, 5, 6, 3, 4, 7, 8, 9, 10, 13, 14, 11, 12, 15, 16, 33, 34, 37, 38, 35, 36, 39, 40, 41, 42, 45, 46, 43, 44, 47, 48, 17, 18, 21, 22, 19, 20, 23, 24, 25, 26, 29, 30, 27, 28, 31, 32, 49, 50, 53, 54, 51, 52, 55, 56, 57, 58, 61, 62, 59, 60, 63, 64]

theorem axisSwap12SectorTargetOrder_length :
    axisSwap12SectorTargetOrder.length = 65 := by
  rfl

def axisSwap12SectorTargetIndex (sourceIndex : Fin 65) : Fin 65 :=
  axisSwap12SectorTargetOrder.get
    (Fin.cast axisSwap12SectorTargetOrder_length.symm sourceIndex)

def axisSwap12StateLinkTransportCheckAt (sourceIndex : Fin 65) : Bool :=
  factorListTransportCheck 2
    (YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization.centralFixedFaceIds 0)
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport.axisSwap12BoundaryRename
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport.axisSwap12BoundaryRename
    (axisSwap12StateSourceFactors sourceIndex)
    (axisSwap12StateMatchedTargetFactors
      (axisSwap12SectorTargetIndex sourceIndex))

theorem axisSwap12SectorTargetOrder_perm :
    axisSwap12SectorTargetOrder.Perm (List.finRange 65) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap12SectorTargetOrder
  decide

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.axisSwap12StateMatchedTargetFactors_perm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12SectorTransportData.axisSwap12SectorTargetOrder_perm
