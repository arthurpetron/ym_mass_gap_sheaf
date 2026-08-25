/-
# Exact finite decisions for the adaptive transition-product margin

The arbitrary-nome finite-capacity compiler reduces every routed off-ray
transition-product certificate to one rational comparison between the shared
ray-coercivity floor and a located minimum of exact edge capacity/load ratios.
This module reflects that comparison into a total finite decision.

At one cutoff, inspection returns either the literal routed transition-product
certificate or a constructive refutation of its exact finite-minimum
comparison.  Thus no finite search remains hidden in the cofinal input.

For a fixed nome and cofinal ray capacity, an adaptive success family may
choose a routing at every cutoff.  The shorter canonical success family asks
only that the executable check succeed for the already constructed canonical
positive routing.  Both compile to the unchanged cofinal transition-product
consumer.

No cofinal success theorem is asserted.  A sequence of individually decidable
finite statements is not replaced by an unproved uniform limit.  No physical
BF4/AF trajectory, strength band, same-object pin, continuum theory, or Clay
conclusion is constructed.  No `Classical.*`, choice, `native_decide`,
`sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor
open YMGap.Continuum.BF4PhysicalSpinCubeRayDirichletCoercivity
open YMGap.Continuum.BF4PhysicalSpinCubeRayReturnFloor

/-! ## 1. One exact finite margin certificate -/

/-- The single rational comparison equivalent to the finite-margin producer
for a fixed ray capacity and a fixed routed carrier. -/
structure CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt
    {w : Q'} (hw : (0 : Q') < w) (K : Nat)
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1 where
  margin_bound :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing

namespace CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt

/-- The checked scalar comparison pays every exact directed-edge load and
constructs the existing finite routed transition-product certificate. -/
def toRoutedConditionalTransitionProductAt
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    {rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K}
    {routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K}
    (data :
      CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt
        hw K rayCapacity routing) :
    CentralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductAt
      hw K rayCapacity routing where
  edge_capacity := fun source hsource target htarget => by
    have hloadNonnegative :=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad_nonnegative
        routing hsource target
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
      data.margin_bound hloadNonnegative
    exact Q'.le_trans' _ _ _ hscaled
      (centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin_mul_load_le_half_conditionalKernel
        routing hsource target htarget)

end CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt

/-! ## 2. Total check and an exact finite obstruction -/

/-- The exact Boolean reflection of the one finite rational margin
comparison. -/
def adaptiveFiniteCapacityMarginCheck
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Bool :=
  decide
    (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing)

theorem adaptiveFiniteCapacityMarginCheck_sound
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (hcheck : adaptiveFiniteCapacityMarginCheck rayCapacity routing = true) :
    centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
        routing := by
  unfold adaptiveFiniteCapacityMarginCheck at hcheck
  exact of_decide_eq_true hcheck

theorem adaptiveFiniteCapacityMarginCheck_complete
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)
    (hmargin :
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
          routing) :
    adaptiveFiniteCapacityMarginCheck rayCapacity routing = true := by
  unfold adaptiveFiniteCapacityMarginCheck
  exact decide_eq_true hmargin

/-- Exact result of inspecting one routed finite cutoff.  The failed branch
retains the decidable rational statement that prevents construction. -/
inductive AdaptiveFiniteCapacityMarginOutcome
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) : Type 1
  | certified
      (certificate :
        CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt
          hw K rayCapacity routing)
  | failed
      (not_margin : Not
        (centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
          centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
            routing))

/-- Compute either the exact finite transition-product input or a refutation
of its scalar minimum comparison. -/
def inspectAdaptiveFiniteCapacityMargin
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K)
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K) :
    AdaptiveFiniteCapacityMarginOutcome rayCapacity routing := by
  by_cases hmargin :
      centralLowerExcitedSpinCubeSharedCoercivityFloor rayCapacity <=
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductFiniteCapacityMargin
          routing
  · exact AdaptiveFiniteCapacityMarginOutcome.certified
      { margin_bound := hmargin }
  · exact AdaptiveFiniteCapacityMarginOutcome.failed hmargin

/-! ## 3. Cofinal adaptive and canonical success families -/

/-- A cofinal family of exact finite checks, allowing the route to depend on
the cutoff.  All finite search is performed by the Boolean field. -/
structure FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  routing : forall K, (hK : rayCapacity.start <= K) ->
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  check_success : forall K, (hK : rayCapacity.start <= K) ->
    adaptiveFiniteCapacityMarginCheck
      (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK) (routing K hK) = true

namespace FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess

def toFiniteCapacityMargin
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (data :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityMargin
      hw rayCapacity where
  routing := data.routing
  margin_bound := fun K hK =>
    adaptiveFiniteCapacityMarginCheck_sound
      (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK) (data.routing K hK)
      (data.check_success K hK)

def toAdaptiveConditionalTransitionProduct
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (data :
      FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      hw rayCapacity :=
  data.toFiniteCapacityMargin.toAdaptiveConditionalTransitionProduct

end FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess

/-- The canonical check uses the already constructed loop-erased positive
routing at the same nome and cutoff. -/
def canonicalFiniteCapacityMarginCheck
    {w : Q'} {hw : (0 : Q') < w} {K : Nat}
    (rayCapacity : CentralLowerExcitedSpinCubeFiniteRayCapacityAt hw K) : Bool :=
  adaptiveFiniteCapacityMarginCheck rayCapacity
    (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K)

/-- The shortest cofinal route: every exact canonical finite check succeeds. -/
structure FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
    {w : Q'} (hw : (0 : Q') < w)
    (rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw) : Type 1 where
  check_success : forall K, (hK : rayCapacity.start <= K) ->
    canonicalFiniteCapacityMarginCheck
      (BF4PhysicalSpinCubeRayDirichletCoercivity.FixedNomeCofinalSpinCubeRayCapacity.finiteCapacityAt
        rayCapacity K hK) = true

namespace FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess

def toAdaptiveCheckSuccess
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (data :
      FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess
      hw rayCapacity where
  routing := fun K _hK =>
    canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      w (Q'.le_of_lt hw) K
  check_success := fun K hK => data.check_success K hK

def toAdaptiveConditionalTransitionProduct
    {w : Q'} {hw : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw}
    (data :
      FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess
        hw rayCapacity) :
    FixedNomeCofinalSpinCubeOffRayResidualAdaptiveConditionalTransitionProduct
      hw rayCapacity :=
  data.toAdaptiveCheckSuccess.toAdaptiveConditionalTransitionProduct

end FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.CentralLowerExcitedSpinCubeOffRayResidualRoutedFiniteCapacityMarginAt.toRoutedConditionalTransitionProductAt
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.adaptiveFiniteCapacityMarginCheck_sound
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.adaptiveFiniteCapacityMarginCheck_complete
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.inspectAdaptiveFiniteCapacityMargin
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.FixedNomeCofinalSpinCubeOffRayResidualAdaptiveFiniteCapacityCheckSuccess.toAdaptiveConditionalTransitionProduct
#print axioms YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDecision.FixedNomeCofinalSpinCubeOffRayResidualCanonicalFiniteCapacityCheckSuccess.toAdaptiveConditionalTransitionProduct
