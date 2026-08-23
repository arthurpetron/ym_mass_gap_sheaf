/-
# Conditional transition-product target for the cutoff-two novel BF4 flow

The pathwise detailed-balance telescope applies to a positive path ending at
the source of a selected directed edge.  This module constructs that prefix
directly from literal membership in the path's directed-edge list.  It then
rewrites every conditional-Harnack summand by the exact product of reverse /
forward conditional transition ratios along the prefix.

This is a structural reduction, not a projective estimate.  No uniform bound
on the transition products, congestion estimate, thermodynamic/continuum
construction, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive prefix extraction from an edge occurrence -/

/-- Data carried by the prefix ending at the source of a selected directed
edge. -/
structure PositiveKernelPrefixAtDirectedEdge {State : Type}
    (kernel : State → State → Q') (support : List State)
    (first : State) (edge : State × State) : Type where
  source_mem : edge.1 ∈ support
  target_mem : edge.2 ∈ support
  pathPrefix :
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
      kernel support first edge.1
  edge_positive : (0 : Q') < kernel edge.1 edge.2

namespace PositiveKernelChainIn

/-- Literal occurrence of a directed edge determines a constructive positive
prefix from the path's first vertex to the edge source. -/
def prefixAtDirectedEdge {State : Type}
    [DecidableEq State]
    {kernel : State → State → Q'} {support : List State} :
    {first last : State} →
      (hfirst : first ∈ support) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          kernel support first last) →
      (edge : State × State) →
      edge ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path →
      PositiveKernelPrefixAtDirectedEdge kernel support first edge
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _,
      _, hedge => by
      simp only [
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges,
        List.not_mem_nil]
        at hedge
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest,
      edge, hedge => by
      change edge ∈
        (first, next) ::
          BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
            rest at hedge
      by_cases hhead : edge = (first, next)
      · subst edge
        exact
          { source_mem := hfirst
            target_mem := hnext
            pathPrefix :=
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl
                first
            edge_positive := positive }
      · have htail : edge ∈
            BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
              rest :=
          (List.mem_cons.mp hedge).resolve_left hhead
        let tailPrefix := prefixAtDirectedEdge hnext rest edge htail
        exact
          { source_mem := tailPrefix.source_mem
            target_mem := tailPrefix.target_mem
            pathPrefix :=
              BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
                positive hnext tailPrefix.pathPrefix
            edge_positive := tailPrefix.edge_positive }

end PositiveKernelChainIn

/-! ## 2. Exact transition-product summand -/

/-- A conditional-Harnack pair term with its stationary endpoint/source ratio
replaced by the exact reverse/forward conditional product along the prefix to
the selected edge source. -/
def cutoffTwoNovelPathPairConditionalTransitionProductTerm
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈ cutoffTwoNovelEndpointPairs later then
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
        (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    if hedge : (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      let pathPrefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (cutoffTwoNovelPathReverseForwardProduct later
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          pathPrefixData.pathPrefix *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0
  else 0

/-- Prefix extraction plus pathwise detailed balance rewrites one exact
conditional-Harnack summand into transition-product form. -/
theorem cutoffTwoNovelPathPairConditionalHarnackTerm_eqv_transitionProduct
    (later source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairConditionalHarnackTerm
        later source target pair ≈
      cutoffTwoNovelPathPairConditionalTransitionProductTerm
        later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalHarnackTerm
    cutoffTwoNovelPathPairConditionalTransitionProductTerm
  rw [dif_pos hpair, dif_pos hpair]
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  change
    (if (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      (cutoffTwoNovelEndpointWeightRatioAtSource later source pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0) ≈
    (if hedge : (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      let pathPrefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (cutoffTwoNovelPathReverseForwardProduct later
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          pathPrefixData.pathPrefix *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0)
  by_cases hedge : (source, target) ∈
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        path
  · rw [if_pos hedge, dif_pos hedge]
    let pathPrefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      path (source, target) hedge
    have hratio :=
      cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct
        later (cutoffTwoNovelEndpointPair_mem_full hpair).1
        pathPrefixData.pathPrefix
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hratio)
  · rw [if_neg hedge, dif_neg hedge]
    exact Q'.eqv_refl 0

/-! ## 3. Summed transition-product target -/

def cutoffTwoNovelConditionalTransitionProductLoad
    (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalTransitionProductTerm
      later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
    (later source target : Nat) :
    cutoffTwoNovelConditionalHarnackLoad later source target ≈
      cutoffTwoNovelConditionalTransitionProductLoad
        later source target := by
  unfold cutoffTwoNovelConditionalHarnackLoad
    cutoffTwoNovelConditionalTransitionProductLoad
  apply listQSum_congr_on
  intro pair hpair
  exact cutoffTwoNovelPathPairConditionalHarnackTerm_eqv_transitionProduct
    later source target pair hpair

/-- Physical edge capacity is equivalent to the fully local
transition-product target. -/
theorem cutoffTwoNovelEdgeCapacity_iff_conditionalTransitionProductTarget
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target) ↔
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalTransitionProductLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) := by
  constructor
  · intro hcapacity
    have hharnack :=
      (cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget
        hsource target).mp hcapacity
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (Q'.eqv_symm
            (cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
              later source target))))
      hharnack
  · intro htransition
    apply
      (cutoffTwoNovelEdgeCapacity_iff_conditionalHarnackTarget
        hsource target).mpr
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
            later source target)))
      htransition

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_transitionProduct
    (later : Nat)
    (htransition : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalTransitionProductLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_conditionalHarnack
  intro source hsource target htarget
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
          later source target)))
    (htransition source hsource target htarget)

structure CutoffTwoCofinalNovelConditionalTransitionProductBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  transition_product : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelConditionalTransitionProductLoad
          (anchor request) source target ≤
      cutoffTwoNovelAllocatedConditionalKernel
        (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalTransitionProductBound

def toCofinalNovelFlowCapacityRatio
    (bound : CutoffTwoCofinalNovelConditionalTransitionProductBound) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_transitionProduct
      (bound.anchor request)
      (bound.transition_product request)

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalTransitionProductBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalTransitionProductBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.PositiveKernelChainIn.prefixAtDirectedEdge
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.cutoffTwoNovelPathPairConditionalHarnackTerm_eqv_transitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.cutoffTwoNovelEdgeCapacity_iff_conditionalTransitionProductTarget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget.CutoffTwoCofinalNovelConditionalTransitionProductBound.toCompletedStrictContractionData
