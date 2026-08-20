/-
# Checked cube-source transport for one spatial-axis swap

The six-face fundamental cube is fixed by every permutation of its three
opposite-face pairs.  This module checks the induced nontrivial permutation
of all 48 genuine lower-link factors.  The checker evaluates the production
SU(2) invariant multiplicities on each empty or unary boundary scope.

This remains a finite cutoff-two result only.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def axisSwap01CubeSourceFactors : List ScopedQFactor :=
  cutoffTwoSourceLinkFactors centralLowerCubeState

theorem axisSwap01CubeSourceFactor_count :
    axisSwap01CubeSourceFactors.length = 48 := by
  decide

/-- Lower-link target indices in source matching order. -/
def axisSwap01LowerLinkTargetOrder : List (Fin 48) :=
  [1, 0, 3, 2, 4, 7, 8, 5, 6, 10, 9, 11,
   12, 15, 14, 13, 28, 17, 18, 19, 31, 21, 22, 23,
   24, 25, 26, 27, 16, 29, 30, 20, 32, 33, 34, 35,
   36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

def axisSwap01MatchedCubeSourceFactors : List ScopedQFactor :=
  reorderFactorsWithLength axisSwap01CubeSourceFactors 48
    axisSwap01CubeSourceFactor_count axisSwap01LowerLinkTargetOrder

theorem axisSwap01LowerLinkTargetOrder_perm :
    axisSwap01LowerLinkTargetOrder.Perm (List.finRange 48) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap01LowerLinkTargetOrder
  decide

theorem axisSwap01MatchedCubeSourceFactors_perm :
    axisSwap01MatchedCubeSourceFactors.Perm axisSwap01CubeSourceFactors :=
  reorderFactorsWithLength_perm axisSwap01CubeSourceFactors 48
    axisSwap01CubeSourceFactor_count axisSwap01LowerLinkTargetOrder
    axisSwap01LowerLinkTargetOrder_perm

theorem axisSwap01CubeSourceFactorListTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename axisSwap01CubeSourceFactors
      axisSwap01MatchedCubeSourceFactors := by
  apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename
  unfold axisSwap01MatchedCubeSourceFactors reorderFactorsWithLength
    axisSwap01LowerLinkTargetOrder axisSwap01CubeSourceFactors
  decide

theorem axisSwap01CubeSourceProduct_eqv
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap01BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct axisSwap01CubeSourceFactors source ≈
      scopedFactorProduct axisSwap01CubeSourceFactors target := by
  exact scopedFactorProduct_eqv_of_listTransport_perm
    axisSwap01CubeSourceFactorListTransport
    axisSwap01MatchedCubeSourceFactors_perm
    source target hagree hbounded

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport.axisSwap01CubeSourceFactorListTransport
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCubeSourceFactorTransport.axisSwap01CubeSourceProduct_eqv
