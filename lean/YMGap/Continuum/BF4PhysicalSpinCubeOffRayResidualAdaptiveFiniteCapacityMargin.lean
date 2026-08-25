/-
# Exact finite capacity margins for adaptive BF4 transition-product routing

The adaptive transition-product target is pointwise over every directed edge
of a finite vacuum sector.  At a fixed cutoff and for any supplied positive
routing, those edge inequalities can be contracted constructively to one
explicit rational margin without introducing the fatal global-kernel floor.

On an edge with positive exact transition-product load, divide its allocated
half conditional-kernel capacity by that exact load.  On an unloaded edge use
the harmless value one.  A positive-load support theorem shows that the
conditional kernel is then strictly positive, so every ratio and their
located finite minimum are positive.  The minimum pays every pointwise edge
inequality.

Consequently a cofinal adaptive product follows from a routing family plus
one scalar comparison at each cutoff: the fixed shared coercivity floor lies
below this exact finite margin.  At the fixed strong-coupling anchor, such a
single fixed-nome family also constructs the one-field dynamic extension from
the preceding compiler.

No cofinal margin bound is inhabited here.  The margin may still decay with
the cutoff, and no routing with a uniform lower bound is asserted.  There is
no physical grouped BF4 trajectory, same-observable limit, completed uniform
spectral gap, continuum Yang--Mills theory, or Clay conclusion.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CentralSpinCubeUniformRayCapacity
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCanonicalAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.FiniteWeightedCartesianInjection

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positivity and support of the exact routed observable -/

private theorem q_nonpos_of_not_pos_local {q : Q'}
    (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  apply Int.not_lt.mp
  intro hnum
  apply hnot
  exact CReal.pos_of_num_pos hnum

/-- After cancellation of the positive stationary source weight, routed
relative traffic remains nonnegative on an actual source. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
        routing source target := by
  let weight := centralPhysicalFiniteWeight w hw K 0 source
  let relative :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
      routing source target
  let flow := centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
    routing source target
  have hweight : (0 : Q') < weight :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hflow : (0 : Q') ≤ flow :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad_nonnegative
      routing source target
  have heq : weight * relative ≈ flow :=
    centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
      routing hsource target
  have hscaled : weight * 0 ≤ weight * relative :=
    Q'.le_trans' _ 0 _
      (Q'.le_of_eqv (Q'.mul_zero_eqv weight))
      (Q'.le_trans' _ flow _ hflow (Q'.ge_of_eqv heq))
  exact Q'.le_of_mul_le_mul_left hscaled hweight

/-- The literal transition-product load is nonnegative; the proof passes
through its exact equality with the same routed relative traffic. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    (0 : Q') ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target := by
  have hrelative :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_nonnegative
      routing hsource target
  have heq :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
      routing hsource target
  exact Q'.le_trans' _ _ _ hrelative (Q'.le_of_eqv heq)

/-- Positive exact transition-product load forces a positive physical
conditional transition on that same directed edge.  This is the support
fact that prevents the sharp ratio from seeing unrelated tiny kernel entries. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat)
    (hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target) :
    (0 : Q') < centralPhysicalFiniteConditionalKernel
      w hw K 0 source target := by
  let relative :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad
      routing source target
  let flow := centralLowerExcitedSpinCubeOffRayResidualRoutedFlowLoad
    routing source target
  have htransition :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_eqv_transitionProductLoad
      routing hsource target
  have hrelative : (0 : Q') < relative :=
    Q'.pos_of_lt_of_le hload (Q'.ge_of_eqv htransition)
  have hweight : (0 : Q') <
      centralPhysicalFiniteWeight w hw K 0 source :=
    centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex hsource
  have hweighted : (0 : Q') <
      centralPhysicalFiniteWeight w hw K 0 source * relative :=
    Q'.mul_pos hweight hrelative
  have hflowEq :
      centralPhysicalFiniteWeight w hw K 0 source * relative ≈ flow :=
    centralPhysicalFiniteWeight_mul_routedRelativeSourceFlowLoad_eqv_flowLoad
      routing hsource target
  have hflow : (0 : Q') < flow :=
    Q'.pos_of_lt_of_le hweighted (Q'.le_of_eqv hflowEq)
  rcases exists_occurrence_of_weightedDirectedEdgeLoad_pos
      (centralLowerExcitedSpinCubeOffRayResidualRoutedFlowOccurrences routing)
      (centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_load_nonnegative
        routing)
      source target hflow with
    ⟨occurrence, hoccurrence, hedge⟩
  have hkernel : (0 : Q') < centralPhysicalFiniteKernel
      w hw K 0 source target := by
    have hpositive :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedOccurrence_kernel_pos
        routing occurrence hoccurrence
    simpa only [hedge] using hpositive
  exact centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
    hsource hkernel

/-! ## 2. A located exact finite margin for any supplied routing -/

/-- Half conditional-kernel capacity divided by the exact transition-product
load, totalized by one on unloaded edges. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) : Q' :=
  if hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target then
    Q'.divPos
      (HalfPow.half *
        centralPhysicalFiniteConditionalKernel w hw K 0 source target)
      (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target)
      hload
  else
    1

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
        routing source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
  by_cases hload : (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
        routing source target
  · rw [dif_pos hload]
    exact Q'.divPos_pos _ _ hload
      (Q'.mul_pos (by decide)
        (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
          routing hsource target hload))
  · rw [dif_neg hload]
    decide

/-- The exact capped finite margin over every ordered pair in the literal
vacuum-sector carrier. -/
def centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) : Q' :=
  listPositiveMinOne
    (fun pair =>
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
        routing pair.1 pair.2)
    (centralPhysicalFiniteVacuumSectorPairs w hw K 0)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K) :
    (0 : Q') <
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
  apply listPositiveMinOne_pos
  intro pair hpair
  rcases pair with ⟨source, target⟩
  unfold centralPhysicalFiniteVacuumSectorPairs at hpair
  have hmembers :=
    (mem_cartesian_iff _ _ (source, target)).mp hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio_pos
      routing hmembers.1 target

/-- The located margin pays every exact transition-product edge load. -/
theorem centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_mul_load_le_half_conditionalKernel
    {w : Q'} {hw : (0 : Q') ≤ w} {K source : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (hsource : source ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (target : Nat)
    (htarget : target ∈
      centralPhysicalFiniteVacuumSectorIndices w hw K 0) :
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
          routing *
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
          routing source target ≤
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel w hw K 0 source target := by
  let load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
      routing source target
  have hloadNonnegative : (0 : Q') ≤ load :=
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
      routing hsource target
  by_cases hload : (0 : Q') < load
  · have hpair : (source, target) ∈
        centralPhysicalFiniteVacuumSectorPairs w hw K 0 := by
      unfold centralPhysicalFiniteVacuumSectorPairs
      exact (mem_cartesian_iff _ _ (source, target)).mpr
        ⟨hsource, htarget⟩
    have hminimum := listPositiveMinOne_le_of_mem
      (fun pair : Nat × Nat =>
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
          routing pair.1 pair.2)
      (centralPhysicalFiniteVacuumSectorPairs w hw K 0)
      (source, target) hpair
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ load
      hminimum hloadNonnegative
    refine Q'.le_trans' _ _ _ hscaled ?_
    change
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
          routing source target * load ≤
        HalfPow.half *
          centralPhysicalFiniteConditionalKernel w hw K 0 source target
    unfold
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio
    change (if h : (0 : Q') < load then
        Q'.divPos
          (HalfPow.half *
            centralPhysicalFiniteConditionalKernel w hw K 0 source target)
          load h
      else 1) * load ≤ _
    rw [dif_pos hload]
    exact Q'.le_of_eqv
      (Q'.divPos_mul_eqv
        (HalfPow.half *
          centralPhysicalFiniteConditionalKernel w hw K 0 source target)
        load hload)
  · have hloadNonpositive : load ≤ 0 :=
      q_nonpos_of_not_pos_local hload
    have hloadZero : load ≈ 0 :=
      Q'.eqv_of_le_le hloadNonpositive hloadNonnegative
    refine Q'.le_trans' _ 0 _ ?_
      (Q'.mul_nonneg _ _ HalfPow.half_nonneg
        (centralPhysicalFiniteConditionalKernel_nonnegative
          w hw K 0 source target))
    exact Q'.le_of_eqv
      (Q'.eqv_trans _
        (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
          routing * 0) _
        (Q'.mul_eqv_congr_left
          (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
            routing)
          load 0 hloadZero)
        (Q'.mul_zero_eqv _))

/-! ## 3. The cofinal product is reduced to one scalar margin comparison -/

/-- A routing family whose exact finite capacity margin pays the unchanged
shared ray-coercivity floor at every cofinal cutoff. -/
structure FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : ∀ K, (hK : rayCapacity.start ≤ K) →
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  margin_bound : ∀ K, (hK : rayCapacity.start ≤ K) →
    centralLowerExcitedSpinCubeSharedCoercivityFloor
        (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
          rayCapacity K hK) ≤
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        (routing K hK)

namespace FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin

/-- The scalar margin bound reconstructs every pointwise edge field of the
existing cofinal adaptive transition-product certificate. -/
def toAdaptiveConditionalTransitionProduct
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      hw rayCapacity where
  routing := family.routing
  product := fun K hK => {
    edge_capacity := fun source hsource target htarget => by
      have hloadNonnegative :=
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
          (family.routing K hK) hsource target
      have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
        (family.margin_bound K hK) hloadNonnegative
      exact Q'.le_trans' _ _ _ hscaled
        (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_mul_load_le_half_conditionalKernel
          (family.routing K hK) hsource target htarget)
  }

/-- Hence the same scalar margin family reaches the existing completed strict
contraction data at the fixed nome. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  family.toAdaptiveConditionalTransitionProduct.toCompletedStrictContractionData
    hw0 hw1

end FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin

/-! ## 4. Fixed-anchor contraction into the dynamic one-field extension -/

abbrev AnchorAdaptiveFiniteCapacityMargin : Type 1 :=
  FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
    anchorCoupling_pos anchorCentralSpinCubeCofinalRayCapacity

/-- At the constant anchor nome, one fixed-nome cofinal margin family can be
reused at every geometric scale and discharges the entire dynamic extension. -/
def AnchorAdaptiveFiniteCapacityMargin.toAnchorGeometricExtension
    (family : AnchorAdaptiveFiniteCapacityMargin) :
    AnchorGeometricAdaptiveTransitionProductExtension where
  transitionProduct := fun _scale =>
    family.toAdaptiveConditionalTransitionProduct

/-- Conditional construction of the existing completed dynamic family from
the exact anchor margin frontier. -/
def AnchorAdaptiveFiniteCapacityMargin.toAnchorGeometricCompletedFamily
    (family : AnchorAdaptiveFiniteCapacityMargin) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily 0 :=
  family.toAnchorGeometricExtension.toCompletedFamily

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedRelativeSourceFlowLoad_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_pos_implies_conditionalKernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductEdgeRatio_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_mul_load_le_half_conditionalKernel
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.toAdaptiveConditionalTransitionProduct
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin.AnchorAdaptiveFiniteCapacityMargin.toAnchorGeometricCompletedFamily
