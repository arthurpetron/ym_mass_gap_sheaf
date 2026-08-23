/-
# Exact transition-product target for symmetric old-to-new BF4 flow

The forward half of the symmetric relative load already has a pathwise
detailed-balance description: its endpoint/source stationary ratio is the
product of reverse/forward conditional ratios along the prefix ending at the
selected edge source.  The reverse half is normalized by the old endpoint as
the selected edge's target.  Extending the extracted prefix through that edge
gives the matching exact product for this target-normalized traffic.

Thus both halves of the old-to-new symmetric relative load are rewritten,
without an inequality or stationary-weight ratio, as explicit finite sums of
conditional transition products.  Payment of their average by the old-to-new
conditional transition supplies the cross field of the symmetric compiler.

The transition-product payment is a named Type-level input and is not inhabited
here.  No uniform capacity estimate, thermodynamic/continuum construction, or
Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalHarnackTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossConditional
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorSimplePathScale
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem divPos_eqv_congr_numerator_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (heq : left ≈ right) :
    Q'.divPos left denominator hdenominator ≈
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_eqv_congr_right _ _
    (Q'.recipPos denominator hdenominator) heq

private theorem divPos_product_eqv_ratio_product_local
    (left right length denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos ((left * right) * length)
        denominator hdenominator ≈
      (Q'.divPos left denominator hdenominator * right) * length := by
  unfold Q'.divPos
  show ((((left * right) * length) *
      Q'.recipPos denominator hdenominator) : Q') ≈
    (((left * Q'.recipPos denominator hdenominator) * right) * length)
  show
    ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).num *
      ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).den : Int)) =
    ((((left * Q'.recipPos denominator hdenominator) * right) *
        length).num *
      ((((left * right) * length) *
        Q'.recipPos denominator hdenominator).den : Int))
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. Expand target-normalized load into endpoint-pair terms -/

/-- One endpoint pair's directed-edge contribution divided by the stationary
mass at the selected edge target. -/
def cutoffTwoNovelPathPairRelativeTargetDemand
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if htarget : target ∈ cutoffTwoEdgeLoadFullStates later then
    Q'.divPos
      (cutoffTwoNovelPathPairEdgeContribution
        later source target pair)
      (cutoffTwoEdgeLoadWeight later target)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) htarget)
  else 0

/-- Division by the target weight distributes exactly over the finite
endpoint-pair expansion of the grouped edge load. -/
theorem cutoffTwoNovelRelativeTargetEdgeLoad_eqv_pairDemandSum
    (later source target : Nat) :
    cutoffTwoNovelRelativeTargetEdgeLoad later source target ≈
      listQSum
        (cutoffTwoNovelPathPairRelativeTargetDemand
          later source target)
        (cutoffTwoNovelEndpointPairs later) := by
  by_cases htarget : target ∈ cutoffTwoEdgeLoadFullStates later
  · have hweight :=
      centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w := cutoffTwoHalfCoupling) (hw := by decide) htarget
    unfold cutoffTwoNovelRelativeTargetEdgeLoad
      cutoffTwoNovelPathPairRelativeTargetDemand
    simp only [dif_pos htarget]
    refine Q'.eqv_trans _
      (Q'.divPos
        (listQSum
          (cutoffTwoNovelPathPairEdgeContribution later source target)
          (cutoffTwoNovelEndpointPairs later))
        (cutoffTwoEdgeLoadWeight later target) hweight) _ ?_ ?_
    · exact divPos_eqv_congr_numerator_local hweight
        (cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
          later source target)
    unfold Q'.divPos
    exact Q'.eqv_symm
      (listQSum_mul_right
        (cutoffTwoNovelPathPairEdgeContribution later source target)
        (Q'.recipPos (cutoffTwoEdgeLoadWeight later target) hweight)
        (cutoffTwoNovelEndpointPairs later))
  · unfold cutoffTwoNovelRelativeTargetEdgeLoad
      cutoffTwoNovelPathPairRelativeTargetDemand
    simp only [dif_neg htarget]
    exact Q'.eqv_symm (listQSum_zero (cutoffTwoNovelEndpointPairs later))

/-! ## 2. The target-normalized Harnack term -/

/-- The exact endpoint/edge-target stationary ratio term for one listed pair
whose path traverses the selected directed edge. -/
def cutoffTwoNovelPathPairConditionalTargetHarnackTerm
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hpair : pair ∈ cutoffTwoNovelEndpointPairs later then
    let path :=
      centralPhysicalFiniteVacuumSectorSimplePositivePath
        cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
        (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (cutoffTwoNovelEndpointPair_mem_full hpair).2
    if (source, target) ∈
        PositiveKernelChainIn.directedEdges path then
      (cutoffTwoNovelEndpointWeightRatioAtSource
          later target pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  else 0

theorem cutoffTwoNovelPathPairRelativeTargetDemand_eqv_harnackTerm
    {later target : Nat}
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later)
    (source : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairRelativeTargetDemand
        later source target pair ≈
      cutoffTwoNovelPathPairConditionalTargetHarnackTerm
        later source target pair := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w := cutoffTwoHalfCoupling) (hw := by decide) htarget
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  unfold cutoffTwoNovelPathPairRelativeTargetDemand
  rw [dif_pos htarget]
  unfold cutoffTwoNovelPathPairConditionalTargetHarnackTerm
  rw [dif_pos hpair]
  change Q'.divPos
      (cutoffTwoNovelPathPairEdgeContribution
        later source target pair)
      (cutoffTwoEdgeLoadWeight later target) hweight ≈
    if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      (cutoffTwoNovelEndpointWeightRatioAtSource
          later target pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge]
    have hcontribution :=
      cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
        later source target pair hpair
    change cutoffTwoNovelPathPairEdgeContribution
        later source target pair ≈
      if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
        (cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0 at hcontribution
    rw [if_pos hedge] at hcontribution
    refine Q'.eqv_trans _
      (Q'.divPos
        ((cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path))
        (cutoffTwoEdgeLoadWeight later target) hweight) _ ?_ ?_
    · exact divPos_eqv_congr_numerator_local hweight hcontribution
    have hratio :
        Q'.divPos
            (cutoffTwoEdgeLoadWeight later pair.1)
            (cutoffTwoEdgeLoadWeight later target) hweight =
          cutoffTwoNovelEndpointWeightRatioAtSource
            later target pair.1 := by
      unfold cutoffTwoNovelEndpointWeightRatioAtSource
      rw [dif_pos htarget]
    rw [← hratio]
    exact divPos_product_eqv_ratio_product_local _ _ _ _ hweight
  · rw [if_neg hedge]
    have hcontribution :=
      cutoffTwoNovelPathPairEdgeContribution_eqv_indicator
        later source target pair hpair
    change cutoffTwoNovelPathPairEdgeContribution
        later source target pair ≈
      if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
        (cutoffTwoEdgeLoadWeight later pair.1 *
            cutoffTwoEdgeLoadWeight later pair.2) *
          Q'.ofNat (PositiveKernelChainIn.edgeLength path)
      else 0 at hcontribution
    rw [if_neg hedge] at hcontribution
    refine Q'.eqv_trans _
      (Q'.divPos 0 (cutoffTwoEdgeLoadWeight later target) hweight) _
      (divPos_eqv_congr_numerator_local hweight hcontribution) ?_
    unfold Q'.divPos
    exact Q'.zero_mul_eqv _

def cutoffTwoNovelConditionalTargetHarnackLoad
    (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalTargetHarnackTerm
      later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelRelativeTargetEdgeLoad_eqv_conditionalTargetHarnackLoad
    {later target : Nat}
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later)
    (source : Nat) :
    cutoffTwoNovelRelativeTargetEdgeLoad later source target ≈
      cutoffTwoNovelConditionalTargetHarnackLoad
        later source target := by
  refine Q'.eqv_trans _
    (listQSum
      (cutoffTwoNovelPathPairRelativeTargetDemand later source target)
      (cutoffTwoNovelEndpointPairs later)) _
    (cutoffTwoNovelRelativeTargetEdgeLoad_eqv_pairDemandSum
      later source target) ?_
  unfold cutoffTwoNovelConditionalTargetHarnackLoad
  apply listQSum_congr_on
  intro pair hpair
  exact cutoffTwoNovelPathPairRelativeTargetDemand_eqv_harnackTerm
    htarget source pair hpair

/-! ## 3. Extend the path prefix through the selected edge -/

/-- The extracted prefix ending at an edge source, extended through that
positive edge to its target. -/
def positiveKernelPrefixThroughEdge {State : Type}
    {kernel : State → State → Q'} {support : List State}
    {first : State} {edge : State × State}
    (prefixData : PositiveKernelPrefixAtDirectedEdge
      kernel support first edge) :
    BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn
      kernel support first edge.2 :=
  BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.trans
    prefixData.pathPrefix
    (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.step
      prefixData.edge_positive prefixData.target_mem
      (BF4PhysicalFiniteVacuumSectorPositiveConnectivity.PositiveKernelChainIn.refl
        edge.2))

/-- The target-Harnack pair term with its endpoint/edge-target stationary ratio
replaced by the exact conditional transition product through the edge. -/
def cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
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
      (cutoffTwoNovelPathReverseForwardProduct later
          (cutoffTwoNovelEndpointPair_mem_full hpair).1
          (positiveKernelPrefixThroughEdge prefixData) *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0
  else 0

theorem cutoffTwoNovelPathPairConditionalTargetHarnackTerm_eqv_transitionProduct
    (later source target : Nat) (pair : Nat × Nat)
    (hpair : pair ∈ cutoffTwoNovelEndpointPairs later) :
    cutoffTwoNovelPathPairConditionalTargetHarnackTerm
        later source target pair ≈
      cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
        later source target pair := by
  unfold cutoffTwoNovelPathPairConditionalTargetHarnackTerm
    cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
  rw [dif_pos hpair, dif_pos hpair]
  let path :=
    centralPhysicalFiniteVacuumSectorSimplePositivePath
      cutoffTwoHalfCoupling (by decide) later 0 pair.1 pair.2
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      (cutoffTwoNovelEndpointPair_mem_full hpair).2
  change
    (if (source, target) ∈ PositiveKernelChainIn.directedEdges path then
      (cutoffTwoNovelEndpointWeightRatioAtSource later target pair.1 *
        cutoffTwoEdgeLoadWeight later pair.2) *
      Q'.ofNat (PositiveKernelChainIn.edgeLength path)
    else 0) ≈
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
    else 0)
  by_cases hedge : (source, target) ∈
      PositiveKernelChainIn.directedEdges path
  · rw [if_pos hedge, dif_pos hedge]
    let prefixData := PositiveKernelChainIn.prefixAtDirectedEdge
      (cutoffTwoNovelEndpointPair_mem_full hpair).1
      path (source, target) hedge
    have hratio :=
      cutoffTwoNovelEndpointWeightRatioAtSource_eqv_pathProduct
        later (cutoffTwoNovelEndpointPair_mem_full hpair).1
        (positiveKernelPrefixThroughEdge prefixData)
    exact Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hratio)
  · rw [if_neg hedge, dif_neg hedge]
    exact Q'.eqv_refl 0

def cutoffTwoNovelConditionalTargetTransitionProductLoad
    (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairConditionalTargetTransitionProductTerm
      later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoNovelConditionalTargetHarnackLoad_eqv_transitionProductLoad
    (later source target : Nat) :
    cutoffTwoNovelConditionalTargetHarnackLoad later source target ≈
      cutoffTwoNovelConditionalTargetTransitionProductLoad
        later source target := by
  unfold cutoffTwoNovelConditionalTargetHarnackLoad
    cutoffTwoNovelConditionalTargetTransitionProductLoad
  apply listQSum_congr_on
  intro pair hpair
  exact cutoffTwoNovelPathPairConditionalTargetHarnackTerm_eqv_transitionProduct
    later source target pair hpair

/-! ## 4. Exact symmetric cross transition-product target -/

def cutoffTwoNovelSymmetricCrossTransitionProductLoad
    (later oldState newState : Nat) : Q' :=
  HalfPow.half *
      cutoffTwoNovelConditionalTransitionProductLoad
        later oldState newState +
    HalfPow.half *
      cutoffTwoNovelConditionalTargetTransitionProductLoad
        later newState oldState

theorem cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_crossTransitionProductLoad
    {later oldState : Nat}
    (hold : oldState ∈ cutoffTwoEdgeLoadOldStates later)
    (newState : Nat) :
    cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
        later oldState newState ≈
      cutoffTwoNovelSymmetricCrossTransitionProductLoad
        later oldState newState := by
  have holdFull : oldState ∈ cutoffTwoEdgeLoadFullStates later :=
    (List.mem_filter.mp hold).1
  unfold cutoffTwoNovelSymmetricRelativeSourceEdgeLoad
    cutoffTwoNovelSymmetricCrossTransitionProductLoad
  apply Q'.add_eqv_congr'
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.eqv_trans _ _ _
        (cutoffTwoNovelRelativeSourceEdgeLoad_eqv_conditionalHarnackLoad
          holdFull newState)
        (cutoffTwoNovelConditionalHarnackLoad_eqv_transitionProductLoad
          later oldState newState))
  · exact Q'.mul_eqv_congr_left HalfPow.half _ _
      (Q'.eqv_trans _ _ _
        (cutoffTwoNovelRelativeTargetEdgeLoad_eqv_conditionalTargetHarnackLoad
          holdFull newState)
        (cutoffTwoNovelConditionalTargetHarnackLoad_eqv_transitionProductLoad
          later newState oldState))

/-- A non-vacuous Type-level witness that the old-to-new conditional
transition pays the exact average of the two conditional transition-product
loads. -/
structure CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt
    (later : Nat) : Type 1 where
  transition_capacity : ∀ oldState,
    oldState ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ newState,
    newState ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSymmetricCrossTransitionProductLoad
            later oldState newState ≤
        cutoffTwoEdgeLoadConditionalKernel later oldState newState

namespace CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt

def toOldNewConditionalCapacityAt
    {later : Nat}
    (capacity :
      CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt later) :
    CutoffTwoNovelSymmetricOldNewConditionalCapacityAt later where
  relative_capacity := fun oldState hold newState hnew => by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_eqv_congr_left
          cutoffTwoNovelSimpleFlowCoercivityFloor _ _
          (cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_crossTransitionProductLoad
            hold newState)))
      (capacity.transition_capacity oldState hold newState hnew)

end CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.cutoffTwoNovelRelativeTargetEdgeLoad_eqv_pairDemandSum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.cutoffTwoNovelPathPairRelativeTargetDemand_eqv_harnackTerm
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.positiveKernelPrefixThroughEdge
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.cutoffTwoNovelPathPairConditionalTargetHarnackTerm_eqv_transitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.cutoffTwoNovelSymmetricRelativeSourceEdgeLoad_eqv_crossTransitionProductLoad
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCrossTransitionProduct.CutoffTwoNovelSymmetricOldNewTransitionProductCapacityAt.toOldNewConditionalCapacityAt
