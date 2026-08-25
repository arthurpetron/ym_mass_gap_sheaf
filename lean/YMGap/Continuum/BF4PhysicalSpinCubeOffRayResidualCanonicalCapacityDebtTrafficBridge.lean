/-
# Endpoint-traffic bridge for canonical BF4 capacity-debt variation

The mapped-path bridge separates physical data drift from route churn, but
its data term still contains two causally different effects: the old endpoint
traffic changes its weights and conditional kernel, while genuinely new
endpoint pairs enter the later residual sum.

This module splits those effects without changing the observable.  At the
later cutoff it filters the literal residual endpoint-pair list according to
whether both endpoints lie in the embedded old vacuum-sector carrier.  The
complement is therefore exactly the new endpoint traffic, including all
multiplicities and the same routed transition-product term.  Finite-sum
partition and distributivity through the matched conditional-kernel capacity
prove that the full bridge debt is the sum of its old-traffic and new-traffic
debts.

The earlier canonical debt is compared first with the later old-traffic debt
on the mapped route.  Adding the exact new-traffic debt reaches the full
bridge debt, and route churn then reaches the later canonical debt.  Thus the
transported-old branch expands into three independently estimable streams:

* same-route old-traffic physical drift;
* genuinely new endpoint traffic; and
* route churn.

Together with the three shell faces, six inverse-square packages contract to
the existing five-package bridge, four-region control, one total tail, and
the completed fixed-anchor family.

No estimate is inhabited here.  The fixed strong-coupling anchor is not the
physical AF/grouped-BF4 trajectory, and no thermodynamic, continuum, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem add_le_add_local
    {a b c d : Q'} (hab : a <= b) (hcd : c <= d) :
    a + c <= b + d :=
  Q'.le_trans' _ _ _
    (Q'.add_le_add_right a b c hab)
    (Q'.add_le_add_left b c d hcd)

private theorem reassoc_cancel_local (u middle residual : Q') :
    ((u + (-middle)) + (middle + residual)) ≈ u + residual := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv u (-middle) (middle + residual)) ?_
  refine Q'.add_eqv_congr_left u
    ((-middle) + (middle + residual)) residual ?_
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-middle) middle residual)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right ((-middle) + middle) 0 residual
      (Q'.neg_add_self_eqv middle)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' residual)

private theorem abs_sub_triangle_local (a b c : Q') :
    Q'.abs (a + -b) <=
      Q'.abs (a + -c) + Q'.abs (c + -b) := by
  have hdecompose : a + -b ≈ (a + -c) + (c + -b) := by
    exact Q'.eqv_symm (reassoc_cancel_local a c (-b))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose))
    (Q'.abs_add_le' (a + -c) (c + -b))

private theorem listQMaxZero_le_of_member_bound_local
    {State : Type} (value : State -> Q') (bound : Q') :
    forall states : List State,
      (0 : Q') <= bound ->
      (forall state, state ∈ states -> value state <= bound) ->
      listQMaxZero value states <= bound
  | [], hbound, _ => hbound
  | head :: tail, hbound, hall => by
      unfold listQMaxZero
      exact (Q'.max'_le_iff' _ _ _).mpr
        ⟨hall head List.mem_cons_self,
          listQMaxZero_le_of_member_bound_local value bound tail hbound
            (fun state hstate =>
              hall state (List.mem_cons_of_mem head hstate))⟩

/-! ## 1. Exact old/new partition of the later residual endpoint traffic -/

/-- Decide whether both demand endpoints belong to the embedded old vacuum
sector.  This predicate partitions the actual later residual endpoint list;
it is not a surrogate list or an independently chosen observable. -/
def anchorTransportedBridgeEndpointPairOldB
    (scale : Nat) (pair : Nat × Nat) : Bool :=
  decide
    (pair.1 ∈ anchorEmbeddedOldIndexCarrier scale ∧
      pair.2 ∈ anchorEmbeddedOldIndexCarrier scale)

/-- The literal later residual endpoint pairs whose two endpoints are old. -/
def anchorTransportedBridgeOldEndpointPairs
    (scale : Nat) : List (Nat × Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1)).filter
    (anchorTransportedBridgeEndpointPairOldB scale)

/-- The literal complementary endpoint traffic introduced by the later
cutoff.  Negating the same Boolean makes the partition exact. -/
def anchorTransportedBridgeNewEndpointPairs
    (scale : Nat) : List (Nat × Nat) :=
  (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1)).filter
    (fun pair => !(anchorTransportedBridgeEndpointPairOldB scale pair))

/-- Later mapped-route load restricted to old endpoint traffic. -/
def anchorTransportedBridgeOldEndpointTrafficLoadOnPair
    (scale : Nat) (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (anchorTransportedCanonicalRoutingAtNext scale) edge.1 edge.2)
    (anchorTransportedBridgeOldEndpointPairs scale)

/-- Later mapped-route load restricted to genuinely new endpoint traffic. -/
def anchorTransportedBridgeNewEndpointTrafficLoadOnPair
    (scale : Nat) (edge : Nat × Nat) : Q' :=
  listQSum
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (anchorTransportedCanonicalRoutingAtNext scale) edge.1 edge.2)
    (anchorTransportedBridgeNewEndpointPairs scale)

/-- The full later bridge load is exactly its old-endpoint and new-endpoint
traffic.  The same transition-product summand, route, and ordered edge occur
in all three terms. -/
theorem anchorTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
    (scale : Nat) (edge : Nat × Nat) :
    anchorRoutedLoadOnPair
        anchorTransportedCanonicalRoutingSequence (scale + 1) edge ≈
      anchorTransportedBridgeOldEndpointTrafficLoadOnPair scale edge +
        anchorTransportedBridgeNewEndpointTrafficLoadOnPair scale edge := by
  unfold anchorRoutedLoadOnPair
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoad
  change listQSum
      (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        (anchorTransportedCanonicalRoutingAtNext scale) edge.1 edge.2)
      (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1)) ≈ _
  exact listQSum_filter_partition
    (centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
      (anchorTransportedCanonicalRoutingAtNext scale) edge.1 edge.2)
    (anchorTransportedBridgeEndpointPairOldB scale)
    (centralLowerExcitedSpinCubeOffRayResidualEndpointPairs
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1))

/-! ## 2. The matched old/new capacity debts -/

/-- Normalize an explicitly supplied routed load by the same physical
conditional-kernel capacity used by the canonical debt. -/
def anchorCapacityDebtFromLoadOnPair
    (scale : Nat) (edge : Nat × Nat) (load : Q') : Q' :=
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
      scale 0 edge.1 edge.2
  if hcapacity : (0 : Q') < capacity then
    Q'.divPos (anchorAdaptiveSharedCoercivityFloor * load)
      capacity hcapacity
  else
    0

/-- The existing routed debt is definitionally the load-parametric debt on
the exact routed load. -/
theorem anchorRoutedCapacityDebtOnPair_eqv_fromLoad
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (edge : Nat × Nat) :
    anchorRoutedCapacityDebtOnPair routing scale edge ≈
      anchorCapacityDebtFromLoadOnPair scale edge
        (anchorRoutedLoadOnPair routing scale edge) := by
  exact Q'.eqv_refl _

/-- Later mapped-route debt carried only by old endpoint traffic. -/
def anchorTransportedBridgeOldEndpointTrafficDebtOnPair
    (scale : Nat) (edge : Nat × Nat) : Q' :=
  anchorCapacityDebtFromLoadOnPair (scale + 1) edge
    (anchorTransportedBridgeOldEndpointTrafficLoadOnPair scale edge)

/-- Later mapped-route debt carried only by genuinely new endpoint traffic. -/
def anchorTransportedBridgeNewEndpointTrafficDebtOnPair
    (scale : Nat) (edge : Nat × Nat) : Q' :=
  anchorCapacityDebtFromLoadOnPair (scale + 1) edge
    (anchorTransportedBridgeNewEndpointTrafficLoadOnPair scale edge)

/-- Distributivity through the one matched capacity denominator makes the
full mapped-route debt exactly the sum of old and new endpoint-traffic debt. -/
theorem anchorTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
    (scale : Nat) (edge : Nat × Nat) :
    anchorRoutedCapacityDebtOnPair
        anchorTransportedCanonicalRoutingSequence (scale + 1) edge ≈
      anchorTransportedBridgeOldEndpointTrafficDebtOnPair scale edge +
        anchorTransportedBridgeNewEndpointTrafficDebtOnPair scale edge := by
  let oldLoad :=
    anchorTransportedBridgeOldEndpointTrafficLoadOnPair scale edge
  let newLoad :=
    anchorTransportedBridgeNewEndpointTrafficLoadOnPair scale edge
  let capacity := HalfPow.half *
    centralPhysicalFiniteConditionalKernel
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
      (scale + 1) 0 edge.1 edge.2
  have hload :
      anchorRoutedLoadOnPair
          anchorTransportedCanonicalRoutingSequence (scale + 1) edge ≈
        oldLoad + newLoad :=
    anchorTransportedBridgeRoutedLoadOnPair_eqv_old_add_new scale edge
  change anchorCapacityDebtFromLoadOnPair (scale + 1) edge
      (anchorRoutedLoadOnPair
        anchorTransportedCanonicalRoutingSequence (scale + 1) edge) ≈ _
  unfold anchorTransportedBridgeOldEndpointTrafficDebtOnPair
  unfold anchorTransportedBridgeNewEndpointTrafficDebtOnPair
  unfold anchorCapacityDebtFromLoadOnPair
  change (if h : (0 : Q') < capacity then
      Q'.divPos
        (anchorAdaptiveSharedCoercivityFloor *
          anchorRoutedLoadOnPair
            anchorTransportedCanonicalRoutingSequence (scale + 1) edge)
        capacity h
    else 0) ≈
    (if h : (0 : Q') < capacity then
      Q'.divPos (anchorAdaptiveSharedCoercivityFloor * oldLoad)
        capacity h
    else 0) +
    (if h : (0 : Q') < capacity then
      Q'.divPos (anchorAdaptiveSharedCoercivityFloor * newLoad)
        capacity h
    else 0)
  by_cases hcapacity : (0 : Q') < capacity
  · simp only [hcapacity, dif_pos]
    unfold Q'.divPos
    refine Q'.eqv_trans _
      ((anchorAdaptiveSharedCoercivityFloor * (oldLoad + newLoad)) *
        Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_eqv_congr_left
          anchorAdaptiveSharedCoercivityFloor _ _ hload)
    refine Q'.eqv_trans _
      (((anchorAdaptiveSharedCoercivityFloor * oldLoad) +
          (anchorAdaptiveSharedCoercivityFloor * newLoad)) *
        Q'.recipPos capacity hcapacity) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ _
        (Q'.mul_add_eqv
          anchorAdaptiveSharedCoercivityFloor oldLoad newLoad)
    exact Q'.add_mul_eqv
      (anchorAdaptiveSharedCoercivityFloor * oldLoad)
      (anchorAdaptiveSharedCoercivityFloor * newLoad)
      (Q'.recipPos capacity hcapacity)
  · simp only [hcapacity]
    exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))

/-! ## 3. Split bridge data drift into old physical drift and new traffic -/

/-- Physical drift with route provenance and endpoint provenance both held
fixed: earlier canonical traffic is compared with later embedded-old traffic
on the mapped earlier route. -/
def anchorTransportedBridgeOldTrafficDataDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let current := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence scale pair
  let laterOld := anchorTransportedBridgeOldEndpointTrafficDebtOnPair
    scale (anchorCurrentPairToNext scale pair)
  Q'.max' (Q'.abs (current + -laterOld))
    (Q'.abs (laterOld + -current))

/-- The exact effect of adding the complementary later endpoint traffic while
holding the later physical kernel and mapped route fixed. -/
def anchorTransportedBridgeNewTrafficDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let laterOld := anchorTransportedBridgeOldEndpointTrafficDebtOnPair
    scale (anchorCurrentPairToNext scale pair)
  let laterFull := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  Q'.max' (Q'.abs (laterOld + -laterFull))
    (Q'.abs (laterFull + -laterOld))

def anchorTransportedBridgeOldTrafficDataDeficitMaximum
    (scale : Nat) : Q' :=
  listQMaxZero
    (anchorTransportedBridgeOldTrafficDataDeficitOnPair scale)
    (anchorVacuumSectorPairs scale)

def anchorTransportedBridgeNewTrafficDeficitMaximum
    (scale : Nat) : Q' :=
  listQMaxZero
    (anchorTransportedBridgeNewTrafficDeficitOnPair scale)
    (anchorVacuumSectorPairs scale)

theorem anchorTransportedBridgeOldTrafficDataDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <=
      anchorTransportedBridgeOldTrafficDataDeficitMaximum scale := by
  unfold anchorTransportedBridgeOldTrafficDataDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorTransportedBridgeOldTrafficDataDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

theorem anchorTransportedBridgeNewTrafficDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorTransportedBridgeNewTrafficDeficitMaximum scale := by
  unfold anchorTransportedBridgeNewTrafficDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorTransportedBridgeNewTrafficDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

theorem anchorTransportedBridgeDataDeficitOnPair_le_traffic_split
    (scale : Nat) (pair : Nat × Nat) :
    anchorTransportedBridgeDataDeficitOnPair scale pair <=
      anchorTransportedBridgeOldTrafficDataDeficitOnPair scale pair +
        anchorTransportedBridgeNewTrafficDeficitOnPair scale pair := by
  let current := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence scale pair
  let laterOld := anchorTransportedBridgeOldEndpointTrafficDebtOnPair
    scale (anchorCurrentPairToNext scale pair)
  let laterFull := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  change Q'.max'
      (Q'.abs (current + -laterFull))
      (Q'.abs (laterFull + -current)) <=
    Q'.max'
        (Q'.abs (current + -laterOld))
        (Q'.abs (laterOld + -current)) +
      Q'.max'
        (Q'.abs (laterOld + -laterFull))
        (Q'.abs (laterFull + -laterOld))
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · exact Q'.le_trans' _ _ _
      (abs_sub_triangle_local current laterFull laterOld)
      (add_le_add_local
        (Q'.le_max'_left _ _)
        (Q'.le_max'_left _ _))
  · have htriangle := abs_sub_triangle_local laterFull current laterOld
    have hmaxima :
        Q'.abs (laterFull + -laterOld) +
            Q'.abs (laterOld + -current) <=
          Q'.max'
              (Q'.abs (laterOld + -laterFull))
              (Q'.abs (laterFull + -laterOld)) +
            Q'.max'
              (Q'.abs (current + -laterOld))
              (Q'.abs (laterOld + -current)) :=
      add_le_add_local
        (Q'.le_max'_right _ _)
        (Q'.le_max'_right _ _)
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hmaxima
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem anchorTransportedBridgeDataDeficitMaximum_le_traffic_split
    (scale : Nat) :
    anchorTransportedBridgeDataDeficitMaximum scale <=
      anchorTransportedBridgeOldTrafficDataDeficitMaximum scale +
        anchorTransportedBridgeNewTrafficDeficitMaximum scale := by
  unfold anchorTransportedBridgeDataDeficitMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.zero_le_add _ _
      (anchorTransportedBridgeOldTrafficDataDeficitMaximum_nonnegative scale)
      (anchorTransportedBridgeNewTrafficDeficitMaximum_nonnegative scale)
  · intro pair hpair
    exact Q'.le_trans' _ _ _
      (anchorTransportedBridgeDataDeficitOnPair_le_traffic_split scale pair)
      (add_le_add_local
        (le_listQMaxZero_of_mem
          (anchorTransportedBridgeOldTrafficDataDeficitOnPair scale)
          (anchorVacuumSectorPairs scale) hpair)
        (le_listQMaxZero_of_mem
          (anchorTransportedBridgeNewTrafficDeficitOnPair scale)
          (anchorVacuumSectorPairs scale) hpair))

/-! ## 4. Six parallel inverse-square packages rejoin the one total tail -/

structure AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl :
    Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  oldTrafficDataCoefficient : Q'
  newTrafficCoefficient : Q'
  routeCoefficient : Q'
  oldTrafficDataCoefficient_nonnegative :
    (0 : Q') <= oldTrafficDataCoefficient
  newTrafficCoefficient_nonnegative : (0 : Q') <= newTrafficCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  oldTrafficData_le : forall scale : Nat,
    anchorTransportedBridgeOldTrafficDataDeficitMaximum scale <=
      oldTrafficDataCoefficient *
        invSqTerm offset offset_at_least_two scale
  newTraffic_le : forall scale : Nat,
    anchorTransportedBridgeNewTrafficDeficitMaximum scale <=
      newTrafficCoefficient *
        invSqTerm offset offset_at_least_two scale
  route_le : forall scale : Nat,
    anchorTransportedBridgeRouteDeficitMaximum scale <=
      routeCoefficient * invSqTerm offset offset_at_least_two scale

def AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl.toBridgeControl
    (control :
      AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl) :
    AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  dataCoefficient :=
    control.oldTrafficDataCoefficient + control.newTrafficCoefficient
  routeCoefficient := control.routeCoefficient
  dataCoefficient_nonnegative :=
    Q'.zero_le_add _ _
      control.oldTrafficDataCoefficient_nonnegative
      control.newTrafficCoefficient_nonnegative
  routeCoefficient_nonnegative := control.routeCoefficient_nonnegative
  data_le := fun scale => by
    let term := invSqTerm
      control.offset control.offset_at_least_two scale
    exact Q'.le_trans' _ _ _
      (anchorTransportedBridgeDataDeficitMaximum_le_traffic_split scale)
      (Q'.le_trans' _ _ _
        (add_le_add_local
          (control.oldTrafficData_le scale)
          (control.newTraffic_le scale))
        (Q'.le_of_eqv
          (Q'.eqv_symm
            (Q'.add_mul_eqv
              control.oldTrafficDataCoefficient
              control.newTrafficCoefficient term))))
  route_le := control.route_le

structure AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl :
    Type 1 where
  transport :
    AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  oldNew_le : forall scale : Nat,
    anchorOldNewReturnCapacityDebtDeficitMaximum scale <=
      oldNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two scale
  newOld_le : forall scale : Nat,
    anchorNewOldReturnCapacityDebtDeficitMaximum scale <=
      newOldCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two scale
  newNew_le : forall scale : Nat,
    anchorNewNewReturnCapacityDebtDeficitMaximum scale <=
      newNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two scale

def AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toBridgeRegionalControl
    (control :
      AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl where
  transport := control.transport.toBridgeControl
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  oldNewCoefficient_nonnegative := control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative := control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative := control.newNewCoefficient_nonnegative
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalControl
    (control :
      AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtInverseSquareControl :=
  control.toBridgeRegionalControl.toTotalControl

def anchorCanonicalCapacityDebtPersistenceOfTrafficInverseSquare
    (control :
      AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toBridgeRegionalControl.toTotalDeficitTail
          tailAllowance <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence :=
  anchorCanonicalCapacityDebtPersistenceOfBridgeInverseSquare
    control.toBridgeRegionalControl tailAllowance tailAllowance_pos initial_closure

def anchorGeometricCompletedFamilyOfTrafficInverseSquare
    (control :
      AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toBridgeRegionalControl.toTotalDeficitTail
          tailAllowance <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  anchorGeometricCompletedFamilyOfBridgeInverseSquare
    control.toBridgeRegionalControl tailAllowance tailAllowance_pos initial_closure

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorTransportedBridgeRoutedLoadOnPair_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorTransportedBridgeDataDeficitOnPair_le_traffic_split
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorTransportedBridgeDataDeficitMaximum_le_traffic_split
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl.toBridgeControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorCanonicalCapacityDebtPersistenceOfTrafficInverseSquare
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge.anchorGeometricCompletedFamilyOfTrafficInverseSquare
