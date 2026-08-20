/-
# Checked common-factor transport for one cube-axis swap

This module certifies the first nonidentity spatial-axis generator on the 44
state-independent factors of the genuine cutoff-two physical interface graph.
The untrusted graph search supplies only two finite permutations.  Lean checks
the coordinate inverse, every scope, every local table, and the factor-list
permutation from the production definitions.

This is finite cutoff-two infrastructure.  It is not a full sector-kernel,
uniform-cutoff, continuum, or mass-gap theorem.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
import YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport

set_option maxRecDepth 500000
set_option maxHeartbeats 100000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeInterfaceContraction
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
open YMGap.Continuum.FiniteScopedFactorCoordinateReindex
open YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate
open YMGap.Continuum.FiniteScopedFactorTableCertificate
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

/-- Swap the first two abstract cube axes on the fixed-interface face IDs.
The map is an involution; identifiers outside the 24-coordinate carrier are
left fixed. -/
def axisSwap01BoundaryRename : Nat → Nat
  | 2 => 4
  | 4 => 2
  | 11 => 13
  | 13 => 11
  | 20 => 40
  | 40 => 20
  | 22 => 38
  | 38 => 22
  | 23 => 41
  | 41 => 23
  | 29 => 49
  | 49 => 29
  | 31 => 47
  | 47 => 31
  | 32 => 50
  | 50 => 32
  | id => id

def cutoffTwoSectorCommonFactors : List ScopedQFactor :=
  cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors

theorem cutoffTwoSectorCommonFactor_count :
    cutoffTwoSectorCommonFactors.length = 44 := by
  decide

/-- Target-factor indices in source matching order. -/
def axisSwap01CommonTargetOrder : List (Fin 44) :=
  [1, 0, 2, 4, 3, 5, 13, 12, 14, 16, 15, 17,
   7, 6, 8, 10, 9, 11, 18, 19, 20, 21, 22, 23,
   24, 26, 25, 27, 29, 28, 30, 31, 36, 33, 37, 38,
   32, 34, 35, 39, 40, 41, 42, 43]

def axisSwap01MatchedCommonFactors : List ScopedQFactor :=
  reorderFactorsWithLength cutoffTwoSectorCommonFactors 44
    cutoffTwoSectorCommonFactor_count axisSwap01CommonTargetOrder

theorem axisSwap01CommonTargetOrder_perm :
    axisSwap01CommonTargetOrder.Perm
      (List.finRange 44) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap01CommonTargetOrder
  decide

theorem axisSwap01MatchedCommonFactors_perm :
    axisSwap01MatchedCommonFactors.Perm cutoffTwoSectorCommonFactors :=
  reorderFactorsWithLength_perm cutoffTwoSectorCommonFactors 44
    cutoffTwoSectorCommonFactor_count axisSwap01CommonTargetOrder
    axisSwap01CommonTargetOrder_perm

/-- All 44 local factor transports are recomputed by the kernel. -/
theorem axisSwap01CommonFactorListTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap01BoundaryRename cutoffTwoSectorCommonFactors
      axisSwap01MatchedCommonFactors := by
  apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap01BoundaryRename axisSwap01BoundaryRename
  unfold axisSwap01MatchedCommonFactors reorderFactorsWithLength
    axisSwap01CommonTargetOrder cutoffTwoSectorCommonFactors
  decide

theorem axisSwap01CommonProduct_eqv
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap01BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct cutoffTwoSectorCommonFactors source ≈
      scopedFactorProduct cutoffTwoSectorCommonFactors target := by
  exact scopedFactorProduct_eqv_of_listTransport_perm
    axisSwap01CommonFactorListTransport
    axisSwap01MatchedCommonFactors_perm
    source target hagree hbounded

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport.axisSwap01CommonFactorListTransport
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwapCommonFactorTransport.axisSwap01CommonProduct_eqv
