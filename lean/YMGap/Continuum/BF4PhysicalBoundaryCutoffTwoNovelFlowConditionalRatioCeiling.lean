/-
# A local ratio ceiling for the cutoff-two novel BF4 flow

The exact conditional transition-product target separates into a local
projective factor on every directed edge and a combinatorial weighted path
sum.  This module formalizes that split.  A one-edge ceiling `rho` bounds the
reverse/forward conditional ratio; induction bounds each prefix product by
`rho ^ prefixLength`; finite summation then yields an explicit ceiling load.

This does not construct a cutoff-uniform `rho` or prove that the ceiling load
fits inside the selected conditional transition.  Those are retained as
separate, honest fields of the final cofinal certificate in this module.
No thermodynamic/continuum construction or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. One-edge ceiling and path-product induction -/

/-- A nonnegative ceiling for every positive reverse/forward conditional
ratio on one fixed cutoff-two vacuum-sector carrier. -/
structure CutoffTwoConditionalReverseForwardCeilingAt
    (later : Nat) (rho : Q') : Type where
  rho_nonnegative : (0 : Q') ≤ rho
  ratio_le : ∀ left
    (hleft : left ∈ cutoffTwoEdgeLoadFullStates later)
    right
    (_hright : right ∈ cutoffTwoEdgeLoadFullStates later),
    ∀ hforward : (0 : Q') <
        cutoffTwoEdgeLoadKernel later left right,
      Q'.divPos
          (cutoffTwoEdgeLoadConditionalKernel later right left)
          (cutoffTwoEdgeLoadConditionalKernel later left right)
          (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
            hleft hforward) ≤
        rho

theorem cutoffTwoNovelPathReverseForwardProduct_pos
    (later : Nat) :
    {first last : Nat} →
      (hfirst : first ∈ cutoffTwoEdgeLoadFullStates later) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          (cutoffTwoEdgeLoadKernel later)
          (cutoffTwoEdgeLoadFullStates later) first last) →
      (0 : Q') <
        cutoffTwoNovelPathReverseForwardProduct later hfirst path
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => by
      unfold cutoffTwoNovelPathReverseForwardProduct
      decide
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      unfold cutoffTwoNovelPathReverseForwardProduct
      exact Q'.mul_pos
        (Q'.divPos_pos _ _
          (cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
            hfirst positive)
          (cutoffTwoEdgeLoadConditionalKernel_reverse_pos_of_kernel_pos
            hfirst hnext positive))
        (cutoffTwoNovelPathReverseForwardProduct_pos
          later hnext rest)

/-- A one-edge projective ceiling raises to exactly the number of edges in
the displayed positive path. -/
theorem cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho) :
    {first last : Nat} →
      (hfirst : first ∈ cutoffTwoEdgeLoadFullStates later) →
      (path :
        BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
          (cutoffTwoEdgeLoadKernel later)
          (cutoffTwoEdgeLoadFullStates later) first last) →
      cutoffTwoNovelPathReverseForwardProduct later hfirst path ≤
        rho ^
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path
  | _, _, _,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl _ => by
      exact Q'.le_refl' 1
  | first, _, hfirst,
      BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      have hfactor := ceiling.ratio_le first hfirst next hnext positive
      have hrest :=
        cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow
          ceiling hnext rest
      have hrestNonnegative : (0 : Q') ≤
          cutoffTwoNovelPathReverseForwardProduct later hnext rest :=
        Q'.le_of_lt
          (cutoffTwoNovelPathReverseForwardProduct_pos later hnext rest)
      have hpowNonnegative : (0 : Q') ≤
          rho ^
            BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
              rest :=
        Q'.pow_nonneg rho ceiling.rho_nonnegative _
      unfold cutoffTwoNovelPathReverseForwardProduct
        BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
      rw [Q'.pow_succ]
      exact Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hfactor hrestNonnegative)
        (Q'.mul_le_mul_of_nonneg_left _ _ _ hrest ceiling.rho_nonnegative)

/-! ## 2. Explicit ceiling load -/

/-- Replace the exact prefix transition product in one pair term by the power
of the supplied one-edge ceiling at that prefix length. -/
def cutoffTwoNovelPathPairConditionalRatioCeilingTerm
    (rho : Q') (later source target : Nat) (pair : Nat × Nat) : Q' :=
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
      let pathPrefixData :=
        PositiveKernelChainIn.prefixAtDirectedEdge
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          path (source, target) hedge
      (rho ^
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            pathPrefixData.pathPrefix *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0
  else 0

theorem cutoffTwoNovelPathPairConditionalTransitionProductTerm_le_ceiling
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairConditionalTransitionProductTerm
        later source target pair ≤
      cutoffTwoNovelPathPairConditionalRatioCeilingTerm
        rho later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalTransitionProductTerm
    cutoffTwoNovelPathPairConditionalRatioCeilingTerm
  rw [dif_pos hpair, dif_pos hpair]
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  change
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
    else 0) ≤
    (if hedge : (source, target) ∈
        BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
          path then
      let pathPrefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (rho ^
          BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            pathPrefixData.pathPrefix *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat
        (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
          path)
    else 0)
  by_cases hedge : (source, target) ∈
      BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences.PositiveKernelChainIn.directedEdges
        path
  · rw [dif_pos hedge, dif_pos hedge]
    let pathPrefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      path (source, target) hedge
    have hproduct :=
      cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow ceiling
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        pathPrefixData.pathPrefix
    have hrightWeight : (0 : Q') ≤ cutoffTwoEdgeLoadWeight later pair.2 :=
      Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (w :=
            BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
          (hw := by decide)
          (cutoffTwoNovelEndpointPair_mem_full hpair).2)
    have hlength : (0 : Q') ≤
        Q'.ofNat
          (BF4PhysicalFiniteVacuumSectorPathLengthEnergy.PositiveKernelChainIn.edgeLength
            path) :=
      ExpNeg.ofNat_nonneg' _
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ hproduct hrightWeight)
        hlength)
      (Q'.le_refl' _)
  · rw [dif_neg hedge, dif_neg hedge]
    exact Q'.le_refl' 0

def cutoffTwoNovelConditionalRatioCeilingLoad
    (rho : Q') (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalRatioCeilingTerm
      rho later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (source target : Nat) :
    cutoffTwoNovelConditionalTransitionProductLoad later source target ≤
      cutoffTwoNovelConditionalRatioCeilingLoad
        rho later source target := by
  unfold cutoffTwoNovelConditionalTransitionProductLoad
    cutoffTwoNovelConditionalRatioCeilingLoad
  apply listQSum_mono
  intro pair hpair
  exact
    cutoffTwoNovelPathPairConditionalTransitionProductTerm_le_ceiling
      ceiling source target pair hpair

/-! ## 3. Ceiling-load compiler -/

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_ratioCeiling
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (hceiling : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelConditionalRatioCeilingLoad
            rho later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_transitionProduct
  intro source hsource target htarget
  have hload :=
    cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
      ceiling source target
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos))
    (hceiling source hsource target htarget)

structure CutoffTwoCofinalNovelConditionalRatioCeilingBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  rho : Nat → Q'
  local_ceiling : ∀ request,
    CutoffTwoConditionalReverseForwardCeilingAt
      (anchor request) (rho request)
  ceiling_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelConditionalRatioCeilingLoad
          (rho request) (anchor request) source target ≤
      cutoffTwoNovelAllocatedConditionalKernel
        (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalRatioCeilingBound

def toCofinalNovelConditionalTransitionProductBound
    (bound : CutoffTwoCofinalNovelConditionalRatioCeilingBound) :
    CutoffTwoCofinalNovelConditionalTransitionProductBound where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  transition_product := fun request source hsource target htarget => by
    have hload :=
      cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
        (bound.local_ceiling request) source target
    exact Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hload
        (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos))
      (bound.ceiling_capacity request source hsource target htarget)

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalRatioCeilingBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelConditionalTransitionProductBound.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalRatioCeilingBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.cutoffTwoNovelPathReverseForwardProduct_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.cutoffTwoNovelPathPairConditionalTransitionProductTerm_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling.CutoffTwoCofinalNovelConditionalRatioCeilingBound.toCompletedStrictContractionData
