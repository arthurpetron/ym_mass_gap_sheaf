/-
# Route-coherent bridge for canonical BF4 capacity-debt variation

The transported-old deficit mixes two distinct effects: the physical data
change with the cutoff, and the canonical loop-erased routes may change.  To
diagnose those effects without separating the routed load from its matching
conditional-kernel capacity, this module constructs an explicit bridge
routing at every positive cutoff.

For old endpoints, the bridge maps the preceding canonical positive path
through the physical cutoff embedding.  Qualitative support persistence
proves every mapped edge remains positive.  If either endpoint is genuinely
new, the bridge uses the ordinary canonical path at the later cutoff.  The
result is a total positive routing on the exact later carrier.

The exact transported-old debt deficit then splits, by the triangle
inequality, into:

* data-plus-new-traffic drift from the earlier canonical routing to the
  mapped-path bridge at the later cutoff; and
* route churn from the mapped-path bridge to the later canonical routing.

Both terms retain the same normalized capacity debt, routed load,
conditional kernel, ordered edge, and carrier recoding.  With inverse-square
bounds, these two terms and the three shell faces are five independently
attackable analytic packages.  They contract to the already verified four-
region control and hence to the one necessary total tail.

No data-drift, route-churn, shell, tail, allowance, or slack estimate is
supplied.  The fixed strong-coupling anchor is not the physical AF/grouped-
BF4 trajectory, and no thermodynamic, continuum, or Clay conclusion is
asserted.  No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom,
or noncomputable declaration is used.
-/

import YMGap.Constructive.CRealAbs
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.SummableInverseSquare
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

/-! ## 1. Map a positive path through the physical cutoff embedding -/

def mapPositiveKernelChainIn
    {State Target : Type}
    {kernel : State -> State -> Q'}
    {replacement : Target -> Target -> Q'}
    {support : List State} {targetSupport : List Target}
    (map : State -> Target)
    (map_mem : forall state,
      state ∈ support -> map state ∈ targetSupport)
    (edgePositive : forall first next,
      first ∈ support -> next ∈ support ->
      (0 : Q') < kernel first next ->
      (0 : Q') < replacement (map first) (map next)) :
    {first last : State} -> first ∈ support ->
      PositiveKernelChainIn kernel support first last ->
      PositiveKernelChainIn replacement targetSupport
        (map first) (map last)
  | _, _, _, PositiveKernelChainIn.refl state =>
      PositiveKernelChainIn.refl (map state)
  | first, _, hfirst,
      PositiveKernelChainIn.step
        (next := next) positive hnext rest =>
      PositiveKernelChainIn.step
        (edgePositive first next hfirst hnext positive)
        (map_mem next hnext)
        (mapPositiveKernelChainIn map map_mem edgePositive hnext rest)

theorem anchorCurrentIndexToNext_kernel_pos
    (scale first next : Nat)
    (hfirst : first ∈ anchorVacuumSectorIndices scale)
    (hnext : next ∈ anchorVacuumSectorIndices scale)
    (hpositive : (0 : Q') <
      centralPhysicalFiniteKernel
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
        scale 0 first next) :
    (0 : Q') <
      centralPhysicalFiniteKernel
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
        (scale + 1) 0
        (anchorCurrentIndexToNext scale first)
        (anchorCurrentIndexToNext scale next) := by
  have hadjacent :
      centralPhysicalFiniteSupportAdjacentB
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 first next = true :=
    (centralPhysicalFiniteSupportAdjacentB_true_iff_kernel_pos
      hfirst hnext).mpr hpositive
  have hmappedAdjacent :=
    centralPhysicalFiniteSupportAdjacentB_cutoffIndexMap
      (w := anchorCoupling)
      (hw := Q'.le_of_lt anchorCoupling_pos)
      (base := scale) (later := scale + 1) (half := 0)
      (row := first) (column := next)
      (Nat.le_succ scale)
      (centralPhysicalFiniteVacuumSectorIndex_lt
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
        scale 0 hfirst)
      (centralPhysicalFiniteVacuumSectorIndex_lt
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
        scale 0 hnext)
      hadjacent
  exact centralPhysicalFiniteKernel_pos_of_supportAdjacent
    (anchorCurrentIndexToNext_mem scale first hfirst)
    (anchorCurrentIndexToNext_mem scale next hnext)
    hmappedAdjacent

def anchorMapPositivePathToNext
    (scale : Nat) {first last : Nat}
    (hfirst : first ∈ anchorVacuumSectorIndices scale)
    (path : PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0)
      (anchorVacuumSectorIndices scale) first last) :
    PositiveKernelChainIn
      (centralPhysicalFiniteKernel
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1) 0)
      (anchorVacuumSectorIndices (scale + 1))
      (anchorCurrentIndexToNext scale first)
      (anchorCurrentIndexToNext scale last) :=
  mapPositiveKernelChainIn
    (anchorCurrentIndexToNext scale)
    (anchorCurrentIndexToNext_mem scale)
    (anchorCurrentIndexToNext_kernel_pos scale)
    hfirst path

theorem anchorCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
    (scale index : Nat)
    (hindex : index ∈ anchorEmbeddedOldIndexCarrier scale) :
    anchorCurrentIndexToNext scale
        (anchorNextIndexToCurrent scale index) = index := by
  unfold anchorEmbeddedOldIndexCarrier at hindex
  unfold anchorNextIndexToCurrent
  exact map_firstMappedPreimageOr_eq_of_mem_map
    (anchorCurrentIndexToNext scale) 0 index
    (anchorVacuumSectorIndices scale) hindex

/-! ## 2. A total mapped-path bridge routing at every positive cutoff -/

def anchorTransportedCanonicalRoutingAtNext (scale : Nat) :
    CentralPhysicalFiniteVacuumSectorPositiveRoutingAt
      anchorCoupling (Q'.le_of_lt anchorCoupling_pos) (scale + 1) where
  path := fun left right hleft hright => by
    by_cases hleftOld : left ∈ anchorEmbeddedOldIndexCarrier scale
    · by_cases hrightOld : right ∈ anchorEmbeddedOldIndexCarrier scale
      · let oldLeft := anchorNextIndexToCurrent scale left
        let oldRight := anchorNextIndexToCurrent scale right
        have holdLeft : oldLeft ∈ anchorVacuumSectorIndices scale := by
          exact anchorNextIndexToCurrent_mem scale left
        have holdRight : oldRight ∈ anchorVacuumSectorIndices scale := by
          exact anchorNextIndexToCurrent_mem scale right
        let oldPath :=
          (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
            anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale).path
              oldLeft oldRight holdLeft holdRight
        have mapped := anchorMapPositivePathToNext
          scale holdLeft oldPath
        have hleftMap :
            anchorCurrentIndexToNext scale oldLeft = left :=
          anchorCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
            scale left hleftOld
        have hrightMap :
            anchorCurrentIndexToNext scale oldRight = right :=
          anchorCurrentIndexToNext_nextToCurrent_of_mem_embeddedOldIndex
            scale right hrightOld
        rw [hleftMap, hrightMap] at mapped
        exact mapped
      · exact
          (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
            anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
            (scale + 1)).path left right hleft hright
    · exact
        (canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          (scale + 1)).path left right hleft hright

def anchorTransportedCanonicalRoutingSequence :
    AnchorAdaptivePositiveRoutingSequence
  | 0 =>
      canonicalCentralPhysicalFiniteVacuumSectorPositiveRoutingAt
        anchorCoupling (Q'.le_of_lt anchorCoupling_pos) 0
  | scale + 1 => anchorTransportedCanonicalRoutingAtNext scale

/-! ## 3. Split transported-old variation into data drift and route churn -/

def anchorTransportedBridgeDataDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let current := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence scale pair
  let bridge := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  Q'.max' (Q'.abs (current + -bridge))
    (Q'.abs (bridge + -current))

def anchorTransportedBridgeRouteDeficitOnPair
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  let bridge := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  let canonical := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  Q'.max' (Q'.abs (bridge + -canonical))
    (Q'.abs (canonical + -bridge))

def anchorTransportedBridgeDataDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorTransportedBridgeDataDeficitOnPair scale)
    (anchorVacuumSectorPairs scale)

def anchorTransportedBridgeRouteDeficitMaximum (scale : Nat) : Q' :=
  listQMaxZero
    (anchorTransportedBridgeRouteDeficitOnPair scale)
    (anchorVacuumSectorPairs scale)

theorem anchorTransportedBridgeDataDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorTransportedBridgeDataDeficitMaximum scale := by
  unfold anchorTransportedBridgeDataDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorTransportedBridgeDataDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

theorem anchorTransportedBridgeRouteDeficitMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <= anchorTransportedBridgeRouteDeficitMaximum scale := by
  unfold anchorTransportedBridgeRouteDeficitMaximum
  apply listQMaxZero_nonnegative
  intro pair
  unfold anchorTransportedBridgeRouteDeficitOnPair
  dsimp only
  exact Q'.le_trans' _ _ _
    (Q'.abs_nonneg _)
    (Q'.le_max'_left _ _)

theorem anchorTransportedCapacityDebtDeficitOnPair_le_bridge_split
    (scale : Nat) (pair : Nat × Nat) :
    anchorTransportedCapacityDebtDeficitOnPair scale pair <=
      anchorTransportedBridgeDataDeficitOnPair scale pair +
        anchorTransportedBridgeRouteDeficitOnPair scale pair := by
  let current := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence scale pair
  let bridge := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  let canonical := anchorRoutedCapacityDebtOnPair
    anchorCanonicalPositiveRoutingSequence
    (scale + 1) (anchorCurrentPairToNext scale pair)
  change Q'.max'
      (Q'.abs (current + -canonical))
      (Q'.abs (canonical + -current)) <=
    Q'.max'
        (Q'.abs (current + -bridge))
        (Q'.abs (bridge + -current)) +
      Q'.max'
        (Q'.abs (bridge + -canonical))
        (Q'.abs (canonical + -bridge))
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · exact Q'.le_trans' _ _ _
      (abs_sub_triangle_local current canonical bridge)
      (add_le_add_local
        (Q'.le_max'_left _ _)
        (Q'.le_max'_left _ _))
  · have htriangle := abs_sub_triangle_local canonical current bridge
    have hmaxima :
        Q'.abs (canonical + -bridge) +
            Q'.abs (bridge + -current) <=
          Q'.max'
              (Q'.abs (bridge + -canonical))
              (Q'.abs (canonical + -bridge)) +
            Q'.max'
              (Q'.abs (current + -bridge))
              (Q'.abs (bridge + -current)) :=
      add_le_add_local
        (Q'.le_max'_right _ _)
        (Q'.le_max'_right _ _)
    exact Q'.le_trans' _ _ _ htriangle
      (Q'.le_trans' _ _ _ hmaxima
        (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem anchorTransportedCapacityDebtDeficitMaximum_le_bridge_split
    (scale : Nat) :
    anchorTransportedCapacityDebtDeficitMaximum scale <=
      anchorTransportedBridgeDataDeficitMaximum scale +
        anchorTransportedBridgeRouteDeficitMaximum scale := by
  unfold anchorTransportedCapacityDebtDeficitMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact Q'.zero_le_add _ _
      (anchorTransportedBridgeDataDeficitMaximum_nonnegative scale)
      (anchorTransportedBridgeRouteDeficitMaximum_nonnegative scale)
  · intro pair hpair
    exact Q'.le_trans' _ _ _
      (anchorTransportedCapacityDebtDeficitOnPair_le_bridge_split
        scale pair)
      (add_le_add_local
        (le_listQMaxZero_of_mem
          (anchorTransportedBridgeDataDeficitOnPair scale)
          (anchorVacuumSectorPairs scale) hpair)
        (le_listQMaxZero_of_mem
          (anchorTransportedBridgeRouteDeficitOnPair scale)
          (anchorVacuumSectorPairs scale) hpair))

/-! ## 4. Five parallel inverse-square packages rejoin the one total tail -/

structure AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl :
    Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  dataCoefficient : Q'
  routeCoefficient : Q'
  dataCoefficient_nonnegative : (0 : Q') <= dataCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  data_le : forall scale : Nat,
    anchorTransportedBridgeDataDeficitMaximum scale <=
      dataCoefficient * invSqTerm offset offset_at_least_two scale
  route_le : forall scale : Nat,
    anchorTransportedBridgeRouteDeficitMaximum scale <=
      routeCoefficient * invSqTerm offset offset_at_least_two scale

def AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl.coefficient
    (control :
      AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl) : Q' :=
  control.dataCoefficient + control.routeCoefficient

theorem AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl.coefficient_nonnegative
    (control :
      AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl) :
    (0 : Q') <= control.coefficient :=
  Q'.zero_le_add _ _
    control.dataCoefficient_nonnegative
    control.routeCoefficient_nonnegative

theorem AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl.transported_le
    (control :
      AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl)
    (scale : Nat) :
    anchorTransportedCapacityDebtDeficitMaximum scale <=
      control.coefficient *
        invSqTerm control.offset control.offset_at_least_two scale := by
  let term := invSqTerm
    control.offset control.offset_at_least_two scale
  exact Q'.le_trans' _ _ _
    (anchorTransportedCapacityDebtDeficitMaximum_le_bridge_split scale)
    (Q'.le_trans' _ _ _
      (add_le_add_local
        (control.data_le scale)
        (control.route_le scale))
      (Q'.le_of_eqv
        (Q'.eqv_symm
          (Q'.add_mul_eqv
            control.dataCoefficient control.routeCoefficient term))))

structure AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl :
    Type 1 where
  transport :
    AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl
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

def AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toRegionalControl
    (control :
      AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtRegionalInverseSquareControl where
  offset := control.transport.offset
  offset_at_least_two := control.transport.offset_at_least_two
  transportCoefficient := control.transport.coefficient
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  transportCoefficient_nonnegative :=
    control.transport.coefficient_nonnegative
  oldNewCoefficient_nonnegative :=
    control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative :=
    control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative :=
    control.newNewCoefficient_nonnegative
  transport_le := control.transport.transported_le
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalControl
    (control :
      AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtInverseSquareControl :=
  control.toRegionalControl.toTotalControl

def AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalDeficitTail
    (control :
      AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtTotalDeficitTail :=
  control.toTotalControl.toTotalDeficitTail

def anchorCanonicalCapacityDebtPersistenceOfBridgeInverseSquare
    (control :
      AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTotalDeficitTail tailAllowance <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence :=
  anchorCanonicalCapacityDebtPersistenceOfInverseSquare
    control.toTotalControl
    tailAllowance tailAllowance_pos initial_closure

def anchorGeometricCompletedFamilyOfBridgeInverseSquare
    (control :
      AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTotalDeficitTail tailAllowance <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  anchorGeometricCompletedFamilyOfInverseSquare
    control.toTotalControl
    tailAllowance tailAllowance_pos initial_closure

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorCurrentIndexToNext_kernel_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorMapPositivePathToNext
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorTransportedCanonicalRoutingAtNext
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorTransportedCapacityDebtDeficitOnPair_le_bridge_split
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorTransportedCapacityDebtDeficitMaximum_le_bridge_split
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.AnchorCanonicalTransportedCapacityDebtBridgeInverseSquareControl.transported_le
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.AnchorCanonicalCapacityDebtBridgeRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge.anchorGeometricCompletedFamilyOfBridgeInverseSquare
