/-
# Expand a novel-flow edge load into endpoint-pair contributions

The decisive capacity checker localizes every failure to one directed BF4
edge.  This module expands the load on that edge back into the endpoint pairs
which created it.  For each novel ordered pair, its contribution is exactly
zero unless the loop-erased positive path traverses the edge; when it does,
the contribution is

  stationaryWeight(left) * stationaryWeight(right) * pathLength.

The grouped load is exactly the finite sum of these terms.  A generic
capacity-allocation theorem then shows how pairwise payments whose total is
bounded by the allocated physical kernel discharge the edge capacity.

No such uniform pairwise payment is supplied here.  No completed uniform gap,
thermodynamic/continuum limit, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityUnitBound

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSimpleFullEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact endpoint-pair expansion of one grouped edge load -/

/-- The contribution of one novel endpoint pair to one directed edge. -/
def cutoffTwoNovelPathPairEdgeContribution
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  weightedDirectedEdgeLoad
    (cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)
    source target

/-- The grouped novel load is exactly the sum of its endpoint-pair
contributions. -/
theorem cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
    (later source target : Nat) :
    cutoffTwoNovelSimpleEdgeLoad later source target ≈
      listQSum
        (cutoffTwoNovelPathPairEdgeContribution later source target)
        (cutoffTwoNovelEndpointPairs later) := by
  unfold cutoffTwoNovelSimpleEdgeLoad
    cutoffTwoNovelSimpleWeightedEdgeOccurrences
    cutoffTwoNovelPathPairEdgeContribution
  exact weightedDirectedEdgeLoad_flatMap_eqv
    (cutoffTwoNovelEndpointPairs later)
    (fun pair =>
      cutoffTwoSimpleWeightedPathOccurrences later pair.1 pair.2)
    source target

/-- On a listed novel endpoint pair, the contribution has the promised exact
stationary-product/path-length indicator formula. -/
theorem cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
    (later source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairEdgeContribution later source target pair ≈
      if (source, target) ∈
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            (BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSectorSimplePositivePath
              BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
              (by decide) later 0 pair.1 pair.2
              (cutoffTwoNovelEndpointPair_mem_full hpair).1
              (cutoffTwoNovelEndpointPair_mem_full hpair).2) then
        (cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat
            (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              (BF4PhysicalFiniteVacuumSectorSimplePathScale.centralPhysicalFiniteVacuumSectorSimplePositivePath
                BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
                (by decide) later 0 pair.1 pair.2
                (cutoffTwoNovelEndpointPair_mem_full hpair).1
                (cutoffTwoNovelEndpointPair_mem_full hpair).2))
      else 0 := by
  unfold cutoffTwoNovelPathPairEdgeContribution
  exact cutoffTwoSimpleWeightedPathEdgeLoad_eqv_indicator
    later pair.1 pair.2 source target
    (cutoffTwoNovelEndpointPair_mem_full hpair).1
    (cutoffTwoNovelEndpointPair_mem_full hpair).2

/-! ## 2. Pairwise allocations compile to edge capacity -/

/-- A decomposition of the allocated capacity of one physical edge into
payments for the novel endpoint pairs whose paths may traverse it. -/
structure CutoffTwoNovelEdgePairAllocation
    (later source target : Nat) : Type 1 where
  payment : Nat × Nat → Q'
  pair_payment : ∀ pair,
    pair ∈ cutoffTwoNovelEndpointPairs later →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelPathPairEdgeContribution
          later source target pair ≤
      payment pair
  total_payment_le :
    listQSum payment (cutoffTwoNovelEndpointPairs later) ≤
      cutoffTwoNovelAllocatedKernel later source target

namespace CutoffTwoNovelEdgePairAllocation

/-- Pairwise payments that fit inside the allocated kernel prove the grouped
edge-capacity inequality consumed by the flow compiler. -/
theorem toEdgeCapacity
    {later source target : Nat}
    (allocation : CutoffTwoNovelEdgePairAllocation
      later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSimpleEdgeLoad later source target ≤
      cutoffTwoNovelAllocatedKernel later source target := by
  have hregroup :=
    cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
      later source target
  have hdistribute :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          listQSum
            (cutoffTwoNovelPathPairEdgeContribution later source target)
            (cutoffTwoNovelEndpointPairs later) ≈
        listQSum
          (fun pair =>
            cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelPathPairEdgeContribution
                later source target pair)
          (cutoffTwoNovelEndpointPairs later) :=
    Q'.eqv_symm
      (listQSum_mul_left
        cutoffTwoNovelSimpleFlowCoercivityFloor
        (cutoffTwoNovelPathPairEdgeContribution later source target)
        (cutoffTwoNovelEndpointPairs later))
  have hleft :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≈
        listQSum
          (fun pair =>
            cutoffTwoNovelSimpleFlowCoercivityFloor *
              cutoffTwoNovelPathPairEdgeContribution
                later source target pair)
          (cutoffTwoNovelEndpointPairs later) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _ hregroup)
      hdistribute
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    (Q'.le_trans' _ _ _
      (listQSum_mono
        (fun pair =>
          cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelPathPairEdgeContribution
              later source target pair)
        allocation.payment
        (cutoffTwoNovelEndpointPairs later)
        allocation.pair_payment)
      allocation.total_payment_le)

end CutoffTwoNovelEdgePairAllocation

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion.cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion.cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion.CutoffTwoNovelEdgePairAllocation.toEdgeCapacity
