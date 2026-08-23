/-
# Conditional-kernel congestion for the novel BF4 flow

The physical kernel used by the canonical-path argument is a symmetric joint
law, while the endpoint weight is its stationary row marginal.  This module
exposes their exact Markov factorization on the actual finite vacuum sector:

  joint(source,target)
    = weight(source) * conditional(source,target).

The old-old half allocation is factored in the same way.  Dividing every
routed endpoint-pair contribution by the strictly positive source weight then
cancels that common stationary factor from the edge-capacity comparison.
Thus the remaining local frontier compares a relative stationary traffic load
directly with an allocated conditional transition probability.

No uniform conditional-congestion estimate, thermodynamic/continuum
construction, or Clay conclusion is asserted here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowEdgeExpansion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowNormalizedCongestion
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact stationary/conditional factorization -/

/-- The row-conditional transition probability on the same indexed carrier as
the novel-flow edge load. -/
def cutoffTwoEdgeLoadConditionalKernel
    (later source target : Nat) : Q' :=
  centralPhysicalConditionalKernel
    BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 source)
    (centralPhysicalFiniteStateAt
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 target)

theorem cutoffTwoEdgeLoadConditionalKernel_nonnegative
    (later source target : Nat) :
    (0 : Q') ≤ cutoffTwoEdgeLoadConditionalKernel later source target := by
  unfold cutoffTwoEdgeLoadConditionalKernel
  exact centralPhysicalConditionalKernel_nonnegative
    (by decide) later 0 _ _

/-- On a genuine vacuum-sector source, stationary weight times its physical
conditional transition is exactly the symmetric joint-kernel entry. -/
theorem cutoffTwoEdgeLoadWeight_mul_conditional_eqv_kernel
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoEdgeLoadWeight later source *
        cutoffTwoEdgeLoadConditionalKernel later source target ≈
      cutoffTwoEdgeLoadKernel later source target := by
  have hsourcePositive := centralPhysicalFiniteStateAt_mem_positive
    BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
    (by decide) later 0
    (centralPhysicalFiniteVacuumSectorIndex_lt
      BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling
      (by decide) later 0 hsource)
  unfold cutoffTwoEdgeLoadWeight cutoffTwoEdgeLoadConditionalKernel
    cutoffTwoEdgeLoadKernel centralPhysicalFiniteWeight
    centralPhysicalFiniteKernel
  exact marginal_mul_conditional_eqv_joint hsourcePositive

theorem cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
    {later source target : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (hkernel : (0 : Q') <
      cutoffTwoEdgeLoadKernel later source target) :
    (0 : Q') <
      cutoffTwoEdgeLoadConditionalKernel later source target := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (hw := by decide) hsource
  unfold cutoffTwoEdgeLoadConditionalKernel
  rw [centralPhysicalConditionalKernel_eq_divPos hweight]
  exact Q'.divPos_pos _ _ hweight hkernel

/-! ## 2. The half allocation is a conditional transition -/

/-- The fraction of the physical edge capacity reserved for novel flow. -/
def cutoffTwoNovelAllocationFraction
    (later source target : Nat) : Q' :=
  if _h :
      source ∈ cutoffTwoEdgeLoadOldStates later ∧
        target ∈ cutoffTwoEdgeLoadOldStates later then
    HalfPow.half
  else 1

theorem cutoffTwoNovelAllocationFraction_pos
    (later source target : Nat) :
    (0 : Q') < cutoffTwoNovelAllocationFraction later source target := by
  unfold cutoffTwoNovelAllocationFraction
  split
  · decide
  · decide

/-- The conditional transition probability after applying the same old-old
half allocation used by the physical edge capacity. -/
def cutoffTwoNovelAllocatedConditionalKernel
    (later source target : Nat) : Q' :=
  cutoffTwoNovelAllocationFraction later source target *
    cutoffTwoEdgeLoadConditionalKernel later source target

private theorem mul_swap_middle_eqv (a b c : Q') :
    a * (b * c) ≈ b * (a * c) := by
  refine Q'.eqv_trans _ ((a * b) * c) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv a b c)) ?_
  refine Q'.eqv_trans _ ((b * a) * c) _
    (Q'.mul_eqv_congr_right _ _ c (Q'.mul_comm_eqv a b)) ?_
  exact Q'.mul_assoc_eqv b a c

private theorem cutoffTwoNovelAllocatedKernel_eqv_fraction_mul_kernel
    (later source target : Nat) :
    cutoffTwoNovelAllocatedKernel later source target ≈
      cutoffTwoNovelAllocationFraction later source target *
        cutoffTwoEdgeLoadKernel later source target := by
  unfold cutoffTwoNovelAllocatedKernel cutoffTwoNovelAllocationFraction
  split
  · exact Q'.eqv_refl _
  · exact Q'.eqv_symm
      (Q'.one_mul_eqv
        (cutoffTwoEdgeLoadKernel later source target))

/-- Exact cancellation-ready form of the allocated joint capacity. -/
theorem cutoffTwoNovelAllocatedKernel_eqv_weight_mul_conditional
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoNovelAllocatedKernel later source target ≈
      cutoffTwoEdgeLoadWeight later source *
        cutoffTwoNovelAllocatedConditionalKernel
          later source target := by
  refine Q'.eqv_trans _
    (cutoffTwoNovelAllocationFraction later source target *
      cutoffTwoEdgeLoadKernel later source target) _
    (cutoffTwoNovelAllocatedKernel_eqv_fraction_mul_kernel
      later source target) ?_
  refine Q'.eqv_trans _
    (cutoffTwoNovelAllocationFraction later source target *
      (cutoffTwoEdgeLoadWeight later source *
        cutoffTwoEdgeLoadConditionalKernel later source target)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (cutoffTwoNovelAllocationFraction later source target) _ _
      (Q'.eqv_symm
        (cutoffTwoEdgeLoadWeight_mul_conditional_eqv_kernel
          hsource target))
  unfold cutoffTwoNovelAllocatedConditionalKernel
  exact mul_swap_middle_eqv
    (cutoffTwoNovelAllocationFraction later source target)
    (cutoffTwoEdgeLoadWeight later source)
    (cutoffTwoEdgeLoadConditionalKernel later source target)

/-- Every literal novel-flow occurrence has a strictly positive conditional
transition in its traversed orientation. -/
theorem cutoffTwoNovelOccurrence_conditionalKernel_pos
    (later : Nat)
    (occurrence :
      BF4PhysicalFiniteVacuumSectorPathEdgeLoad.WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later) :
    (0 : Q') < cutoffTwoEdgeLoadConditionalKernel
      later occurrence.1.1 occurrence.1.2 := by
  have hfull := cutoffTwoNovelOccurrence_mem_full
    later occurrence hoccurrence
  exact cutoffTwoEdgeLoadConditionalKernel_pos_of_kernel_pos
    hfull.1
    (cutoffTwoNovelOccurrence_kernel_pos later occurrence hoccurrence)

theorem cutoffTwoNovelOccurrence_allocatedConditionalKernel_pos
    (later : Nat)
    (occurrence :
      BF4PhysicalFiniteVacuumSectorPathEdgeLoad.WeightedDirectedEdgeOccurrence Nat)
    (hoccurrence : occurrence ∈
      cutoffTwoNovelSimpleWeightedEdgeOccurrences later) :
    (0 : Q') < cutoffTwoNovelAllocatedConditionalKernel
      later occurrence.1.1 occurrence.1.2 := by
  unfold cutoffTwoNovelAllocatedConditionalKernel
  exact Q'.mul_pos
    (cutoffTwoNovelAllocationFraction_pos
      later occurrence.1.1 occurrence.1.2)
    (cutoffTwoNovelOccurrence_conditionalKernel_pos
      later occurrence hoccurrence)

/-! ## 3. Cancel the source stationary mass from routed traffic -/

/-- One endpoint pair's edge demand divided by the stationary mass of the
edge source.  It is totalized by zero away from the finite vacuum sector. -/
def cutoffTwoNovelPathPairRelativeSourceDemand
    (later source target : Nat) (pair : Nat × Nat) : Q' :=
  if hsource : source ∈ cutoffTwoEdgeLoadFullStates later then
    Q'.divPos
      (cutoffTwoNovelPathPairEdgeContribution
        later source target pair)
      (cutoffTwoEdgeLoadWeight later source)
      (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
        (w :=
          BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
        (hw := by decide) hsource)
  else 0

theorem cutoffTwoEdgeLoadWeight_mul_relativePairDemand_eqv_contribution
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) (pair : Nat × Nat) :
    cutoffTwoEdgeLoadWeight later source *
        cutoffTwoNovelPathPairRelativeSourceDemand
          later source target pair ≈
      cutoffTwoNovelPathPairEdgeContribution
        later source target pair := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (hw := by decide) hsource
  unfold cutoffTwoNovelPathPairRelativeSourceDemand
  rw [dif_pos hsource]
  exact Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv
      (cutoffTwoEdgeLoadWeight later source)
      (Q'.divPos
        (cutoffTwoNovelPathPairEdgeContribution
          later source target pair)
        (cutoffTwoEdgeLoadWeight later source) hweight))
    (Q'.divPos_mul_eqv _ _ hweight)

/-- The entire edge load after cancelling its common source stationary mass. -/
def cutoffTwoNovelRelativeSourceEdgeLoad
    (later source target : Nat) : Q' :=
  listQSum
    (cutoffTwoNovelPathPairRelativeSourceDemand
      later source target)
    (cutoffTwoNovelEndpointPairs later)

theorem cutoffTwoEdgeLoadWeight_mul_relativeSourceEdgeLoad_eqv_load
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    cutoffTwoEdgeLoadWeight later source *
        cutoffTwoNovelRelativeSourceEdgeLoad later source target ≈
      cutoffTwoNovelSimpleEdgeLoad later source target := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        cutoffTwoEdgeLoadWeight later source *
          cutoffTwoNovelPathPairRelativeSourceDemand
            later source target pair)
      (cutoffTwoNovelEndpointPairs later)) _ ?_ ?_
  · unfold cutoffTwoNovelRelativeSourceEdgeLoad
    exact Q'.eqv_symm
      (listQSum_mul_left
        (cutoffTwoEdgeLoadWeight later source)
        (cutoffTwoNovelPathPairRelativeSourceDemand
          later source target)
        (cutoffTwoNovelEndpointPairs later))
  refine Q'.eqv_trans _
    (listQSum
      (cutoffTwoNovelPathPairEdgeContribution later source target)
      (cutoffTwoNovelEndpointPairs later)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _hpair
    exact cutoffTwoEdgeLoadWeight_mul_relativePairDemand_eqv_contribution
      hsource target pair
  exact Q'.eqv_symm
    (cutoffTwoNovelSimpleEdgeLoad_eqv_pairContributionSum
      later source target)

private theorem le_iff_of_eqv_positive_common_left
    {weight left right reducedLeft reducedRight : Q'}
    (hweight : (0 : Q') < weight)
    (hleft : left ≈ weight * reducedLeft)
    (hright : right ≈ weight * reducedRight) :
    left ≤ right ↔ reducedLeft ≤ reducedRight := by
  constructor
  · intro h
    have hscaled : weight * reducedLeft ≤ weight * reducedRight :=
      Q'.le_trans' _ left _ (Q'.ge_of_eqv hleft)
        (Q'.le_trans' _ right _ h (Q'.le_of_eqv hright))
    exact Q'.le_of_mul_le_mul_left hscaled hweight
  · intro h
    have hscaled := Q'.mul_le_mul_of_nonneg_left
      reducedLeft reducedRight weight h (Q'.le_of_lt hweight)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.ge_of_eqv hright))

/-- The physical edge-capacity inequality is equivalent, after exact
stationary-source cancellation, to a conditional-transition congestion
inequality. -/
theorem cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion
    {later source : Nat}
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat) :
    (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedKernel later source target) ↔
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelRelativeSourceEdgeLoad later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) := by
  have hweight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (hw := by decide) hsource
  have hloadFactor :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≈
        cutoffTwoEdgeLoadWeight later source *
          (cutoffTwoNovelSimpleFlowCoercivityFloor *
            cutoffTwoNovelRelativeSourceEdgeLoad
              later source target) := by
    refine Q'.eqv_trans _
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
        (cutoffTwoEdgeLoadWeight later source *
          cutoffTwoNovelRelativeSourceEdgeLoad
            later source target)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (Q'.eqv_symm
          (cutoffTwoEdgeLoadWeight_mul_relativeSourceEdgeLoad_eqv_load
            hsource target))
    exact mul_swap_middle_eqv
      cutoffTwoNovelSimpleFlowCoercivityFloor
      (cutoffTwoEdgeLoadWeight later source)
      (cutoffTwoNovelRelativeSourceEdgeLoad later source target)
  exact le_iff_of_eqv_positive_common_left hweight hloadFactor
    (cutoffTwoNovelAllocatedKernel_eqv_weight_mul_conditional
      hsource target)

/-! ## 4. Conditional congestion compiles to the completed gap -/

theorem cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_relativeConditional
    (later : Nat)
    (hrelative : ∀ source,
      source ∈ cutoffTwoEdgeLoadFullStates later →
      ∀ target,
      target ∈ cutoffTwoEdgeLoadFullStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelRelativeSourceEdgeLoad
            later source target ≤
        cutoffTwoNovelAllocatedConditionalKernel
          later source target) :
    cutoffTwoNovelSimpleFlowCoercivityFloor ≤
      cutoffTwoNovelFiniteFlowCapacityFloor later := by
  apply cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_congestion
  intro source hsource target htarget
  apply (cutoffTwoNovelEdgeCapacity_iff_normalizedCongestion
    later source target).mp
  exact
    (cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion
      hsource target).mpr
      (hrelative source hsource target htarget)

structure CutoffTwoCofinalNovelConditionalCongestionBound : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  relative_capacity : ∀ request source,
    source ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    ∀ target,
    target ∈ cutoffTwoEdgeLoadFullStates (anchor request) →
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRelativeSourceEdgeLoad
          (anchor request) source target ≤
      cutoffTwoNovelAllocatedConditionalKernel
        (anchor request) source target

namespace CutoffTwoCofinalNovelConditionalCongestionBound

def toCofinalNovelFlowCapacityRatio
    (bound : CutoffTwoCofinalNovelConditionalCongestionBound) :
    CutoffTwoCofinalNovelFlowCapacityRatio where
  anchor := bound.anchor
  anchor_ge := bound.anchor_ge
  fixed_floor_le := fun request =>
    cutoffTwoNovelFiniteFlowCapacityFloor_ge_of_relativeConditional
      (bound.anchor request)
      (bound.relative_capacity request)

def toCompletedStrictContractionData
    (bound : CutoffTwoCofinalNovelConditionalCongestionBound) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w :=
        BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors.cutoffTwoHalfCoupling)
      (by decide) (by decide) 0 :=
  bound.toCofinalNovelFlowCapacityRatio.toCompletedStrictContractionData

end CutoffTwoCofinalNovelConditionalCongestionBound

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.cutoffTwoEdgeLoadWeight_mul_conditional_eqv_kernel
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.cutoffTwoNovelAllocatedKernel_eqv_weight_mul_conditional
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.cutoffTwoEdgeLoadWeight_mul_relativeSourceEdgeLoad_eqv_load
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.cutoffTwoNovelEdgeCapacity_iff_relativeConditionalCongestion
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowConditionalCongestion.CutoffTwoCofinalNovelConditionalCongestionBound.toCompletedStrictContractionData
