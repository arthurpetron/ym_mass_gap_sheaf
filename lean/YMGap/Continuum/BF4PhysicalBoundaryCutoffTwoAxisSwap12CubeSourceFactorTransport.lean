/-
# Checked cube-source transport for one spatial-axis swap

The six-face fundamental cube is fixed by every permutation of its three
opposite-face pairs.  This module checks the induced nontrivial permutation
of all 48 genuine lower-link factors.  The checker evaluates the production
SU(2) invariant multiplicities on each empty or unary boundary scope.

This remains a finite cutoff-two result only.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def axisSwap12CubeSourceFactors : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors centralLowerCubeState

theorem axisSwap12CubeSourceFactor_count :
    axisSwap12CubeSourceFactors.length = 48 := by
  decide

/-- Lower-link target indices in source matching order. -/
def axisSwap12LowerLinkTargetOrder : List (Fin 48) :=
  [0, 4, 5, 6, 1, 2, 3, 8, 7, 9, 19, 16, 12, 18, 14, 15, 11, 17, 13, 10, 20, 21, 22, 23, 24, 25, 26, 27, 28, 31, 30, 29, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

def axisSwap12MatchedCubeSourceFactors : List ScopedQFactor :=
  reorderFactorsWithLength axisSwap12CubeSourceFactors 48
    axisSwap12CubeSourceFactor_count axisSwap12LowerLinkTargetOrder

theorem axisSwap12LowerLinkTargetOrder_perm :
    axisSwap12LowerLinkTargetOrder.Perm (List.finRange 48) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap12LowerLinkTargetOrder
  decide

theorem axisSwap12MatchedCubeSourceFactors_perm :
    axisSwap12MatchedCubeSourceFactors.Perm axisSwap12CubeSourceFactors :=
  reorderFactorsWithLength_perm axisSwap12CubeSourceFactors 48
    axisSwap12CubeSourceFactor_count axisSwap12LowerLinkTargetOrder
    axisSwap12LowerLinkTargetOrder_perm

theorem axisSwap12CubeSourceFactorListTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename axisSwap12CubeSourceFactors
      axisSwap12MatchedCubeSourceFactors := by
  apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
  unfold axisSwap12MatchedCubeSourceFactors reorderFactorsWithLength
    axisSwap12LowerLinkTargetOrder axisSwap12CubeSourceFactors
  decide

theorem axisSwap12CubeSourceProduct_eqv
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap12BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct axisSwap12CubeSourceFactors source ≈
      scopedFactorProduct axisSwap12CubeSourceFactors target := by
  exact scopedFactorProduct_eqv_of_listTransport_perm
    axisSwap12CubeSourceFactorListTransport
    axisSwap12MatchedCubeSourceFactors_perm
    source target hagree hbounded

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport.axisSwap12CubeSourceFactorListTransport
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CubeSourceFactorTransport.axisSwap12CubeSourceProduct_eqv
