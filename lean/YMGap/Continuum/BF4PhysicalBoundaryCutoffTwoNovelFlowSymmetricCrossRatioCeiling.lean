/-
# One-edge ratio ceiling for symmetric old-to-new BF4 flow

The exact symmetric cross target is an average of two finite transition-product
loads.  The existing one-edge reverse/forward ceiling bounds the forward
source-prefix product.  This module applies the same ceiling to the reverse
target-prefix product, whose constructive chain includes the selected edge.

Both estimates combine into an explicit symmetric ceiling load.  A fixed-scale
Type-level certificate carrying a one-edge ceiling and payment of that load
contracts to the exact transition-product certificate and hence to the
old-to-new field of the symmetric capacity compiler.

Neither the ceiling nor its payment is constructed here.  No uniform
old-to-new or new--new capacity estimate, thermodynamic/continuum construction,
or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalRatioCeiling
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

/-! ## 1. Ceiling for the target-prefix product -/

/-- Replace the exact transition product through the selected edge by the
matching power of the supplied one-edge ceiling. -/
def cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
    (rho : Q') (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈ cutoffTwoNovelEndpointPairs later then
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    if hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (rho ^
          PositiveKernelChainIn.edgeLength
            (positiveKernelPrefixThroughEdge prefixData) *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  else 0

theorem cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm_le_ceiling
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
        later source target pair ≤
      cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
        rho later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
    cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
  rw [dif_pos hpair, dif_pos hpair]
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  change
    (if hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (cutoffTwoNovelPathReverseForwardProduct later
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          (positiveKernelPrefixThroughEdge prefixData) *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0) ≤
    (if hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path then
      let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        path (source, target) hedge
      (rho ^
          PositiveKernelChainIn.edgeLength
            (positiveKernelPrefixThroughEdge prefixData) *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0)
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [dif_pos hedge, dif_pos hedge]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      path (source, target) hedge
    have hproduct :=
      cutoffTwoNovelPathReverseForwardProduct_le_ceilingPow ceiling
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (positiveKernelPrefixThroughEdge prefixData)
    have hrightWeight :
        (0 : Q') ≤ cutoffTwoEdgeLoadWeight later pair.2 :=
      Q'.le_of_lt
        (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
          (w := cutoffTwoHalfCoupling) (hw := by decide)
          (cutoffTwoNovelEndpointPair_mem_full hpair).2)
    have hlength :
        (0 : Q') ≤ Q'.ofNat (PositiveKernelChainIn.edgeLength path) :=
      ExpNeg.ofNat_nonneg' _
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hproduct hrightWeight)
      hlength
  · rw [dif_neg hedge, dif_neg hedge]
    exact Q'.le_refl' 0

def cutoffTwoNovelConditionalTargetRatioCeilingLoad
    (rho : Q') (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalTargetRatioCeilingTerm
      rho later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelConditionalTargetTransitionProductLoad_le_ratioCeilingLoad
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (source target : Nat) :
    cutoffTwoNovelConditionalTargetTransitionProductLoad
        later source target ≤
      cutoffTwoNovelConditionalTargetRatioCeilingLoad
        rho later source target := by
  unfold cutoffTwoNovelConditionalTargetTransitionProductLoad
    cutoffTwoNovelConditionalTargetRatioCeilingLoad
  apply listQSum_mono
  intro pair hpair
  exact
    cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm_le_ceiling
      ceiling source target pair hpair

/-! ## 2. Symmetric ceiling load and compiler -/

def cutoffTwoNovelSymmetricCrossRatioCeilingLoad
    (rho : Q') (later oldState newState : Nat) : Q' :=
  HalfPow.half *
      cutoffTwoNovelConditionalRatioCeilingLoad
        rho later oldState newState +
    HalfPow.half *
      cutoffTwoNovelConditionalTargetRatioCeilingLoad
        rho later newState oldState

theorem cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_ratioCeilingLoad
    {later : Nat} {rho : Q'}
    (ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho)
    (oldState newState : Nat) :
    cutoffTwoNovelSymmetricCrossTransitionProductLoad
        later oldState newState ≤
      cutoffTwoNovelSymmetricCrossRatioCeilingLoad
        rho later oldState newState := by
  unfold cutoffTwoNovelSymmetricCrossTransitionProductLoad
    cutoffTwoNovelSymmetricCrossRatioCeilingLoad
  exact Q'.add_le_add
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalTransitionProductLoad_le_ratioCeilingLoad
        ceiling oldState newState)
      HalfPow.half_nonneg)
    (Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
      (cutoffTwoNovelConditionalTargetTransitionProductLoad_le_ratioCeilingLoad
        ceiling newState oldState)
      HalfPow.half_nonneg)

/-- A non-vacuous fixed-cutoff witness carrying both the local one-edge ratio
ceiling and payment of the resulting symmetric old-to-new ceiling load. -/
structure CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt
    (later : Nat) : Type 1 where
  rho : Q'
  local_ceiling : CutoffTwoConditionalReverseForwardCeilingAt later rho
  ceiling_capacity : ∀ oldState,
    oldState ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ newState,
    newState ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricCrossRatioCeilingLoad
            rho later oldState newState ≤
        cutoffTwoEdgeLoadConditionalKernel later oldState newState

namespace CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt

def toTransitionProductCapacityAt
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt later) :
    CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt later where
  transition_capacity := fun oldState hold newState hnew => by
    have hload :=
      cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_ratioCeilingLoad
        capacity.local_ceiling oldState newState
    have hscaled := Q'.mul_le_mul_of_nonneg_left _ _
      cutoffTwoNovelSimpleFlowCoercivityFloor hload
      (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
    exact Q'.le_trans' _ _ _ hscaled
      (capacity.ceiling_capacity oldState hold newState hnew)

def toOldNewConditionalCapacityAt
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt later) :
    YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional.CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later :=
  capacity.toTransitionProductCapacityAt.toOldNewConditionalCapacityAt

end CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm_le_ceiling
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.cutoffTwoNovelConditionalTargetTransitionProductLoad_le_ratioCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.cutoffTwoNovelSymmetricCrossTransitionProductLoad_le_ratioCeilingLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt.toTransitionProductCapacityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossRatioCeiling.CutoffTwoNovelSymmetricOldNewRatioCeilingCapacityAt.toOldNewConditionalCapacityAt
