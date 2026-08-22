/-
# Checked common-factor transport for one cube-axis swap

This module certifies the second adjacent spatial-axis generator on the 44
state-independent factors of the genuine cutoff-two physical interface graph.
The untrusted graph search supplies only two finite permutations.  Lean checks
the coordinate inverse, every scope, every local table, and the factor-list
permutation from the production definitions.

This is finite cutoff-two infrastructure.  It is not a full sector-kernel,
uniform-cutoff, continuum, or mass-gap theorem.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSectorFactorGraph
import YMGap.Continuum.FiniteScopedFactorLocalReindexCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport

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

/-- Swap the last two abstract cube axes on the fixed-interface face IDs.
The map is an involution; identifiers outside the 24-coordinate carrier are
left fixed. -/
def axisSwap12BoundaryRename : Nat → Nat
  | 4 => 5
  | 5 => 4
  | 11 => 20
  | 13 => 23
  | 14 => 22
  | 20 => 11
  | 22 => 14
  | 23 => 13
  | 40 => 41
  | 41 => 40
  | 47 => 56
  | 49 => 59
  | 50 => 58
  | 56 => 47
  | 58 => 50
  | 59 => 49
  | id => id

def cutoffTwoSectorCommonFactors : List ScopedQFactor :=
  cutoffTwoBoundaryHeatFactors ++ cutoffTwoCubeFixedLinkFactors

theorem cutoffTwoSectorCommonFactor_count :
    cutoffTwoSectorCommonFactors.length = 44 := by
  decide

/-- Target-factor indices in source matching order. -/
def axisSwap12CommonTargetOrder : List (Fin 44) :=
  [0, 2, 1, 6, 8, 7, 3, 5, 4, 9, 10, 11, 12, 14, 13, 18, 20, 19, 15, 17, 16, 21, 22, 23, 24, 25, 27, 26, 31, 29, 32, 28, 30, 33, 34, 35, 36, 39, 40, 37, 38, 41, 42, 43]

def axisSwap12MatchedCommonFactors : List ScopedQFactor :=
  reorderFactorsWithLength cutoffTwoSectorCommonFactors 44
    cutoffTwoSectorCommonFactor_count axisSwap12CommonTargetOrder

theorem axisSwap12CommonTargetOrder_perm :
    axisSwap12CommonTargetOrder.Perm
      (List.finRange 44) := by
  apply finListPerm_of_check
  unfold finListPermutationCheck axisSwap12CommonTargetOrder
  decide

theorem axisSwap12MatchedCommonFactors_perm :
    axisSwap12MatchedCommonFactors.Perm cutoffTwoSectorCommonFactors :=
  reorderFactorsWithLength_perm cutoffTwoSectorCommonFactors 44
    cutoffTwoSectorCommonFactor_count axisSwap12CommonTargetOrder
    axisSwap12CommonTargetOrder_perm

/-- All 44 local factor transports are recomputed by the kernel. -/
theorem axisSwap12CommonFactorListTransport :
    FactorListTransport 2 (centralFixedFaceIds 0)
      axisSwap12BoundaryRename cutoffTwoSectorCommonFactors
      axisSwap12MatchedCommonFactors := by
  apply factorListTransport_of_check 2 (centralFixedFaceIds 0)
    axisSwap12BoundaryRename axisSwap12BoundaryRename
  unfold axisSwap12MatchedCommonFactors reorderFactorsWithLength
    axisSwap12CommonTargetOrder cutoffTwoSectorCommonFactors
  decide

theorem axisSwap12CommonProduct_eqv
    (source target : EdgeLabelling)
    (hagree : LabellingsAgreeUnder (centralFixedFaceIds 0)
      axisSwap12BoundaryRename source target)
    (hbounded : ∀ id, id ∈ centralFixedFaceIds 0 → source id < 3) :
    scopedFactorProduct cutoffTwoSectorCommonFactors source ≈
      scopedFactorProduct cutoffTwoSectorCommonFactors target := by
  exact scopedFactorProduct_eqv_of_listTransport_perm
    axisSwap12CommonFactorListTransport
    axisSwap12MatchedCommonFactors_perm
    source target hagree hbounded

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport.axisSwap12CommonFactorListTransport
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAxisSwap12CommonFactorTransport.axisSwap12CommonProduct_eqv
