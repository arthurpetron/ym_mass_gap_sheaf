/-
# A support-aware automatic lower proxy for adaptive BF4 capacity margins

The exact finite capacity margin is a minimum of half conditional-kernel
capacity divided by the literal routed transition-product load.  This module
constructs a smaller explicit positive margin directly from the same routing:

* take the finite minimum of the conditional kernel only on edges carrying
  positive routed load, using one on unloaded edges;
* take the finite maximum of the exact routed loads; and
* divide half the supported-kernel floor by one plus that load maximum.

The resulting rational is positive and lies below every exact edge ratio,
hence below the exact finite margin.  At the fixed strong-coupling anchor this
removes the free `marginLower` and `marginLower_le_exact` fields from the
preceding normalized-debt compiler.  A routing sequence with summable debt
variation, a total budget from cutoff zero, and enough initial slack therefore
compiles to the same completed geometric dynamic family.

No routing or debt-variation certificate is inhabited here.  The proxy may
still decay with the cutoff.  The fixed anchor is not an asymptotically free
or physical grouped BF4 trajectory, and no thermodynamic limit, continuum
Yang--Mills theory, or Clay conclusion is asserted.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy

set_option maxRecDepth 1000000
set_option maxHeartbeats 500000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

private theorem listPositiveMinOne_lower_bound_local
    {State : Type} (value : State → Q') (candidate : Q') :
    ∀ states : List State,
      candidate ≤ 1 →
      (∀ state, state ∈ states → candidate ≤ value state) →
      candidate ≤ listPositiveMinOne value states
  | [], hunit, _ => hunit
  | first :: rest, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value first ≤ listPositiveMinOne value rest
      · rw [if_pos hle]
        exact hall first List.mem_cons_self
      · rw [if_neg hle]
        exact listPositiveMinOne_lower_bound_local value candidate rest hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem first hstate))

private theorem listPositiveMinOne_unit_upper_local
    {State : Type} (value : State → Q') :
    ∀ states : List State,
      listPositiveMinOne value states ≤ 1
  | [] => Q'.le_refl' 1
  | _first :: rest =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_unit_upper_local value rest)

private theorem listQMaxZero_zero_le_local
    {State : Type} (value : State → Q') :
    ∀ states : List State, (0 : Q') ≤ listQMaxZero value states
  | [] => Q'.le_refl' 0
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (listQMaxZero_zero_le_local value tail)
        (Q'.le_max'_right _ _)

/-! ## 1. The conditional-kernel floor on the literal routed support -/

/-- Retain the physical conditional kernel exactly on edges with positive
routed transition-product load; use one on every unloaded edge. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  if _hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target then
    centralPhysicalFiniteConditionalKernel w hw K 0 source target
  else
    1

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
  by_cases hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target
  · rw [dif_pos hload]
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
        routing hsource target hload
  · rw [dif_neg hload]
    decide

/-- The located positive conditional-kernel floor restricted to the exact
routed support. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) : Q' :=
  listPositiveMinOne
    (fun pair =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
        routing pair.1 pair.2)
    (centralPhysicalFiniteVacuumSectorPairs w hw K 0)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
  apply listPositiveMinOne_pos
  intro pair hpair
  rcases pair with ⟨source, target⟩
  unfold centralPhysicalFiniteVacuumSectorPairs at hpair
  have hmembers :=
    (mem_cartesian_iff _ _ (source, target)).mp hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate_pos
      routing hmembers.1 target

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
        routing ≤ (1 : Q') := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
  exact listPositiveMinOne_unit_upper_local _ _

/-- On a positively loaded sector edge, the support-aware floor lies below
that edge's physical conditional kernel. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_le_conditionalKernel_of_load_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
        routing ≤
      centralPhysicalFiniteConditionalKernel w hw K 0 source target := by
  have hpair : (source, target) ∈
      centralPhysicalFiniteVacuumSectorPairs w hw K 0 := by
    unfold centralPhysicalFiniteVacuumSectorPairs
    exact (mem_cartesian_iff _ _ (source, target)).mpr
      ⟨hsource, htarget⟩
  have hminimum := listPositiveMinOne_le_of_mem
    (fun pair : Nat × Nat =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
        routing pair.1 pair.2)
    (centralPhysicalFiniteVacuumSectorPairs w hw K 0)
    (source, target) hpair
  simpa only [
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor,
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate,
    dif_pos hload] using hminimum

/-! ## 2. The exact routed-load maximum and automatic margin proxy -/

/-- Package the exact routed load as a function on ordered pairs.  Keeping
this function opaque prevents the finite-maximum proof from repeatedly
normalizing the full dependent routing term. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (pair : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
    routing pair.1 pair.2

/-- The located maximum of the literal routed transition-product loads over
the finite vacuum-sector carrier. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) : Q' :=
  listQMaxZero
    (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
      routing)
    (centralPhysicalFiniteVacuumSectorPairs w hw K 0)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
  exact listQMaxZero_zero_le_local _ _

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_le_maximum
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (pair : Nat × Nat)
    (hpair : pair ∈ centralPhysicalFiniteVacuumSectorPairs w hw K 0) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
        routing pair ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
  exact le_listQMaxZero_of_mem _ _ hpair

/-- A positive load denominator that avoids choosing whether the maximum is
itself positive. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) : Q' :=
  1 +
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
      routing

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
  exact Q'.pos_add_nonneg (by decide)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum_nonnegative
      routing)

/-- The automatic support-aware capacity-margin lower proxy. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) : Q' :=
  Q'.divPos
    (HalfPow.half *
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
        routing)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
      routing)
    (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator_pos
      routing)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
  exact Q'.divPos_pos _ _ _
    (Q'.mul_pos (by decide)
      (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
        routing))

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_one
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
        routing ≤ (1 : Q') := by
  let floor :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
      routing
  let maximum :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
      routing
  let denominator :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
      routing
  have hfloor0 : (0 : Q') ≤ floor := Q'.le_of_lt
    (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
      routing)
  have hfloor1 : floor ≤ (1 : Q') :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_le_one
      routing
  have hnumerator : HalfPow.half * floor ≤ (1 : Q') := by
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      HalfPow.half 1 floor (by decide) hfloor0
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv (Q'.one_mul_eqv floor)) hfloor1)
  have hmaximum0 : (0 : Q') ≤ maximum :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum_nonnegative
      routing
  have honeDenominator : (1 : Q') ≤ denominator := by
    unfold denominator
    unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
    exact Q'.add_le_self_of_nonneg 1 maximum hmaximum0
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hnumerator
    (Q'.le_trans' _ _ _ honeDenominator
      (Q'.ge_of_eqv (Q'.one_mul_eqv denominator)))

/-- The automatic proxy lies below the exact edge ratio on every ordered pair
of the literal finite vacuum sector. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_edgeRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
        routing ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
        routing source target := by
  let load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
      routing source target
  let floor :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
      routing
  let maximum :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
      routing
  let denominator :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
      routing
  let proxy :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
      routing
  by_cases hload : (0 : Q') < load
  · have hpair : (source, target) ∈
        centralPhysicalFiniteVacuumSectorPairs w hw K 0 := by
      unfold centralPhysicalFiniteVacuumSectorPairs
      exact (mem_cartesian_iff _ _ (source, target)).mpr
        ⟨hsource, htarget⟩
    have hloadMaxOnPair :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_le_maximum
        routing (source, target) hpair
    have hloadMax : load ≤ maximum := by
      change
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
            routing (source, target) ≤
          centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
            routing
      exact hloadMaxOnPair
    have hmaximumDenominator : maximum ≤ denominator := by
      unfold denominator
      unfold
        centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityDenominator
      have hstep := Q'.add_le_self_of_nonneg maximum 1
        (by decide : (0 : Q') ≤ 1)
      exact Q'.le_trans' _ _ _ hstep
        (Q'.le_of_eqv (Q'.add_comm_eqv maximum 1))
    have hloadDenominator : load ≤ denominator :=
      Q'.le_trans' _ _ _ hloadMax hmaximumDenominator
    have hproxy0 : (0 : Q') ≤ proxy := Q'.le_of_lt
      (centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos
        routing)
    have hscaled : proxy * load ≤ proxy * denominator :=
      Q'.mul_le_mul_of_nonneg_left load denominator proxy
        hloadDenominator hproxy0
    have hrecover : proxy * denominator ≈ HalfPow.half * floor := by
      unfold proxy
      unfold
        centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
      exact Q'.divPos_mul_eqv _ _ _
    have hfloorKernel : floor ≤
        centralPhysicalFiniteConditionalKernel w hw K 0 source target :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_le_conditionalKernel_of_load_pos
        routing hsource target htarget hload
    have hnumerator : HalfPow.half * floor ≤
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel w hw K 0 source target :=
      Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hfloorKernel
        HalfPow.half_nonneg
    have hmul : proxy * load ≤
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel w hw K 0 source target :=
      Q'.le_trans' _ _ _ hscaled
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hrecover) hnumerator)
    unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
    change proxy ≤
      (if h : (0 : Q') < load then
        Q'.divPos
          (HalfPow.half *
            centralPhysicalFiniteConditionalKernel w hw K 0 source target)
          load h
      else 1)
    rw [dif_pos hload]
    exact Q'.le_divPos_of_mul_le _ load hload hmul
  · unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
    change proxy ≤ (if h : (0 : Q') < load then
      Q'.divPos
        (HalfPow.half *
          centralPhysicalFiniteConditionalKernel w hw K 0 source target)
        load h
      else 1)
    rw [dif_neg hload]
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_one
        routing

/-- The support-aware proxy is a kernel-checked lower bound for the exact
finite capacity margin from the same routing and carrier. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_finiteCapacityMargin
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
        routing ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
  apply listPositiveMinOne_lower_bound_local
  · exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_one
        routing
  · intro pair hpair
    rcases pair with ⟨source, target⟩
    unfold centralPhysicalFiniteVacuumSectorPairs at hpair
    have hmembers :=
      (mem_cartesian_iff _ _ (source, target)).mp hpair
    exact
      centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_edgeRatio
        routing hmembers.1 target hmembers.2

/-! ## 3. Fixed-anchor debt persistence with no free lower proxy -/

/-- The automatic support-aware margin proxy for a selected anchor routing at
one cutoff. -/
def anchorAdaptiveSupportCapacityMarginLower
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower
    (routing K)

theorem anchorAdaptiveSupportCapacityMarginLower_pos
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    (0 : Q') < anchorAdaptiveSupportCapacityMarginLower routing K :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos
    (routing K)

theorem anchorAdaptiveSupportCapacityMarginLower_le_exact
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) :
    anchorAdaptiveSupportCapacityMarginLower routing K ≤
      anchorAdaptiveFiniteCapacityMarginAt routing K :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_finiteCapacityMargin
    (routing K)

/-- The normalized debt stream after fixing the automatic support-aware
proxy.  Naming it keeps the persistence certificate from repeatedly reducing
the full proxy and its positivity witness. -/
def anchorAdaptiveSupportCapacityDebt
    (routing : AnchorAdaptivePositiveRoutingSequence) (K : Nat) : Q' :=
  anchorAdaptiveFiniteCapacityDebt
    (anchorAdaptiveSupportCapacityMarginLower routing)
    (anchorAdaptiveSupportCapacityMarginLower_pos routing) K

/-- Compile fixed-anchor persistence after deriving the positive lower proxy
from the routing itself.  The caller supplies only the routing and normalized
debt variation/budget data; there is no free margin or comparison field. -/
def anchorAdaptiveSupportCapacityDebtVariation
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (variation : SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt routing))
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero : variation.tailControl.tailRate budget = 0)
    (initial_closure :
      anchorAdaptiveSupportCapacityDebt routing 0 + budget ≤ (1 : Q')) :
    AnchorAdaptiveFiniteCapacityDebtVariation where
  routing := routing
  marginLower := anchorAdaptiveSupportCapacityMarginLower routing
  marginLower_pos := anchorAdaptiveSupportCapacityMarginLower_pos routing
  marginLower_le_exact := anchorAdaptiveSupportCapacityMarginLower_le_exact
    routing
  variation := by
    change SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt routing)
    exact variation
  budget := budget
  budget_pos := budget_pos
  budget_from_zero := budget_from_zero
  initial_closure := by
    change anchorAdaptiveSupportCapacityDebt routing 0 + budget ≤
      (1 : Q')
    exact initial_closure

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor_le_conditionalKernel_of_load_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_le_maximum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_edgeRatio
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.centralLowerExcitedSpinCubeOffRayResidualRoutedSupportCapacityMarginLower_le_finiteCapacityMargin
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy.anchorAdaptiveSupportCapacityDebtVariation
