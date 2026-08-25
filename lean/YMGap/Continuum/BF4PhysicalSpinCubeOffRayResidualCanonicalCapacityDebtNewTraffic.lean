/-
# Exact nonnegative new-traffic debt for the canonical BF4 bridge

The endpoint-traffic bridge measures the effect of adding genuinely new
endpoint pairs by a two-sided absolute debt deficit.  The full bridge debt is
already the exact sum of old-traffic and new-traffic debts.  To make the new
analytic package as sharp as that identity permits, this module proves that
every routed transition-product summand is nonnegative, hence the filtered
new-traffic load and its matched capacity debt are nonnegative.

Consequently the symmetric old-to-full deficit is bounded by the exact
new-traffic debt itself.  Its located maximum is therefore controlled by the
located maximum of a literal nonnegative complementary debt, with no factor
two and no unmatched kernel floor.  An inverse-square estimate on this exact
debt compiles into the preceding six-stream traffic bridge and then into the
one total tail.

No estimate is inhabited here.  The fixed strong-coupling anchor is not the
physical AF/grouped-BF4 trajectory, and no thermodynamic, continuum, or Clay
conclusion is asserted.  No `Classical.*`, choice, `native_decide`, `sorry`,
custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeOccurrences
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthEnergy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalPathwiseDetailedBalance
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalTransitionProductTarget
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlow
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.InverseSquareAntitoneTailControl
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

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

private theorem add_sub_left_eqv_right (left right : Q') :
    (left + right) + -left ≈ right := by
  refine Q'.eqv_trans _ ((-left) + (left + right)) _
    (Q'.add_comm_eqv (left + right) (-left)) ?_
  refine Q'.eqv_trans _ (((-left) + left) + right) _
    (Q'.eqv_symm (Q'.add_assoc_eqv (-left) left right)) ?_
  refine Q'.eqv_trans _ (0 + right) _
    (Q'.add_eqv_congr_right ((-left) + left) 0 right
      (Q'.neg_add_self_eqv left)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' right)

private theorem left_sub_add_eqv_neg_right (left right : Q') :
    left + -(left + right) ≈ -right := by
  refine Q'.eqv_trans _ (left + ((-left) + (-right))) _ ?_ ?_
  · exact Q'.add_eqv_congr_left left _ _
      (Q'.neg_add_eqv left right)
  refine Q'.eqv_trans _ ((left + (-left)) + (-right)) _
    (Q'.eqv_symm (Q'.add_assoc_eqv left (-left) (-right))) ?_
  refine Q'.eqv_trans _ (0 + (-right)) _
    (Q'.add_eqv_congr_right (left + (-left)) 0 (-right)
      (Q'.add_neg_self_eqv left)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-right))

/-! ## 1. Positivity of every literal routed transition-product summand -/

theorem centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct_nonnegative
    (w : Q') (hw : (0 : Q') <= w) (K : Nat) :
    {first last : Nat} ->
      (hfirst : first ∈
        centralPhysicalFiniteVacuumSectorIndices w hw K 0) ->
      (path : PositiveKernelChainIn
        (centralPhysicalFiniteKernel w hw K 0)
        (centralPhysicalFiniteVacuumSectorIndices w hw K 0)
        first last) ->
      (0 : Q') <=
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
          w hw K hfirst path
  | first, _, hfirst, PositiveKernelChainIn.refl _ => by
      change (0 : Q') <= (1 : Q')
      decide
  | first, _, hfirst,
      PositiveKernelChainIn.step
        (next := next) positive hnext rest => by
      unfold
        centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct
      exact Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (Q'.divPos_pos _ _
            (centralPhysicalFiniteConditionalKernel_pos_of_kernel_pos
              hfirst positive)
            (centralPhysicalFiniteConditionalKernel_reverse_pos_of_kernel_pos
              hfirst hnext positive)))
        (centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct_nonnegative
          w hw K hnext rest)

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_nonnegative
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (left right : Nat)
    (hleft : left ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (hright : right ∈ centralPhysicalFiniteVacuumSectorIndices w hw K 0)
    (source target : Nat) :
    (0 : Q') <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
        routing left right hleft hright source target := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity
  apply weightedDirectedEdgeLoad_nonnegative
  · intro occurrence hoccurrence
    obtain ⟨edge, _hedge, heq⟩ := List.mem_map.mp hoccurrence
    rw [← heq]
    exact (by decide : (0 : Q') <= (1 : Q'))

theorem centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
    {w : Q'} {hw : (0 : Q') <= w} {K : Nat}
    (routing : CentralPhysicalFiniteVacuumSectorPositiveRoutingAt w hw K)
    (source target : Nat) (pair : Nat × Nat) :
    (0 : Q') <=
      centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
        routing source target pair := by
  unfold
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm
  by_cases hpair : pair ∈
      centralLowerExcitedSpinCubeOffRayResidualEndpointPairs w hw K
  · rw [dif_pos hpair]
    let hfull :=
      centralLowerExcitedSpinCubeOffRayResidualEndpointPair_mem_sector hpair
    let path := routing.path pair.1 pair.2 hfull.1 hfull.2
    by_cases hedge : (source, target) ∈
        PositiveKernelChainIn.directedEdges path
    · rw [dif_pos hedge]
      dsimp only
      exact Q'.mul_nonneg _ _
        (Q'.mul_nonneg _ _
          (Q'.mul_nonneg _ _
            (centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct_nonnegative
              w hw K hfull.1
              (PositiveKernelChainIn.prefixAtDirectedEdge
                hfull.1 path (source, target) hedge).pathPrefix)
            (Q'.le_of_lt
              (centralPhysicalFiniteWeight_pos_of_vacuumSectorIndex
                hfull.2)))
          (ExpNeg.ofNat_nonneg'
            (PositiveKernelChainIn.edgeLength path)))
        (centralLowerExcitedSpinCubeOffRayResidualRoutedDirectedEdgeMultiplicity_nonnegative
          routing pair.1 pair.2 hfull.1 hfull.2 source target)
    · rw [dif_neg hedge]
      exact Q'.le_refl' 0
  · rw [dif_neg hpair]
    exact Q'.le_refl' 0

/-! ## 2. The complementary load and debt are nonnegative -/

theorem anchorTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
    (scale : Nat) (edge : Nat × Nat) :
    (0 : Q') <=
      anchorTransportedBridgeNewEndpointTrafficLoadOnPair scale edge := by
  unfold anchorTransportedBridgeNewEndpointTrafficLoadOnPair
  apply listQSum_nonnegative_on
  intro pair _hpair
  exact
    centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
      (anchorTransportedCanonicalRoutingAtNext scale) edge.1 edge.2 pair

theorem anchorCapacityDebtFromLoadOnPair_nonnegative
    (scale : Nat) (edge : Nat × Nat) (load : Q')
    (hload : (0 : Q') <= load) :
    (0 : Q') <= anchorCapacityDebtFromLoadOnPair scale edge load := by
  unfold anchorCapacityDebtFromLoadOnPair
  dsimp only
  by_cases hcapacity : (0 : Q') <
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          anchorCoupling (Q'.le_of_lt anchorCoupling_pos)
          scale 0 edge.1 edge.2
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt anchorAdaptiveSharedCoercivityFloor_pos) hload)
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

theorem anchorTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
    (scale : Nat) (edge : Nat × Nat) :
    (0 : Q') <=
      anchorTransportedBridgeNewEndpointTrafficDebtOnPair scale edge :=
  anchorCapacityDebtFromLoadOnPair_nonnegative
    (scale + 1) edge
    (anchorTransportedBridgeNewEndpointTrafficLoadOnPair scale edge)
    (anchorTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
      scale edge)

/-! ## 3. The symmetric new-traffic deficit contracts to the exact debt -/

theorem anchorTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt
    (scale : Nat) (pair : Nat × Nat) :
    anchorTransportedBridgeNewTrafficDeficitOnPair scale pair <=
      anchorTransportedBridgeNewEndpointTrafficDebtOnPair
        scale (anchorCurrentPairToNext scale pair) := by
  let edge := anchorCurrentPairToNext scale pair
  let oldDebt :=
    anchorTransportedBridgeOldEndpointTrafficDebtOnPair scale edge
  let newDebt :=
    anchorTransportedBridgeNewEndpointTrafficDebtOnPair scale edge
  let fullDebt := anchorRoutedCapacityDebtOnPair
    anchorTransportedCanonicalRoutingSequence (scale + 1) edge
  have hsplit : fullDebt ≈ oldDebt + newDebt :=
    anchorTransportedBridgeCapacityDebtOnPair_eqv_old_add_new scale edge
  have hnewNonnegative : (0 : Q') <= newDebt :=
    anchorTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative scale edge
  have holdSubFull : oldDebt + -fullDebt ≈ -newDebt := by
    refine Q'.eqv_trans _ (oldDebt + -(oldDebt + newDebt)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left oldDebt _ _
        (Q'.neg_eqv_congr _ _ hsplit)
    exact left_sub_add_eqv_neg_right oldDebt newDebt
  have hfullSubOld : fullDebt + -oldDebt ≈ newDebt := by
    refine Q'.eqv_trans _ ((oldDebt + newDebt) + -oldDebt) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ (-oldDebt) hsplit
    exact add_sub_left_eqv_right oldDebt newDebt
  change Q'.max'
      (Q'.abs (oldDebt + -fullDebt))
      (Q'.abs (fullDebt + -oldDebt)) <= newDebt
  apply (Q'.max'_le_iff' _ _ _).mpr
  constructor
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ (Q'.abs (-newDebt)) _
        (Q'.abs_eqv_congr holdSubFull)
        (Q'.eqv_trans _ (Q'.abs newDebt) _
          (Q'.abs_neg' newDebt)
          (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hnewNonnegative))))
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ (Q'.abs newDebt) _
        (Q'.abs_eqv_congr hfullSubOld)
        (Q'.eqv_of_eq (ExpNeg.abs_of_nonneg hnewNonnegative)))

def anchorTransportedBridgeNewEndpointTrafficDebtMaximum
    (scale : Nat) : Q' :=
  listQMaxZero
    (fun pair =>
      anchorTransportedBridgeNewEndpointTrafficDebtOnPair
        scale (anchorCurrentPairToNext scale pair))
    (anchorVacuumSectorPairs scale)

theorem anchorTransportedBridgeNewEndpointTrafficDebtMaximum_nonnegative
    (scale : Nat) :
    (0 : Q') <=
      anchorTransportedBridgeNewEndpointTrafficDebtMaximum scale := by
  unfold anchorTransportedBridgeNewEndpointTrafficDebtMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact anchorTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
    scale (anchorCurrentPairToNext scale pair)

theorem anchorTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
    (scale : Nat) :
    anchorTransportedBridgeNewTrafficDeficitMaximum scale <=
      anchorTransportedBridgeNewEndpointTrafficDebtMaximum scale := by
  unfold anchorTransportedBridgeNewTrafficDeficitMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      anchorTransportedBridgeNewEndpointTrafficDebtMaximum_nonnegative scale
  · intro pair hpair
    exact Q'.le_trans' _ _ _
      (anchorTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt scale pair)
      (le_listQMaxZero_of_mem
        (fun item =>
          anchorTransportedBridgeNewEndpointTrafficDebtOnPair
            scale (anchorCurrentPairToNext scale item))
        (anchorVacuumSectorPairs scale) hpair)

/-! ## 4. Exact-debt estimates compile into the six-stream traffic bridge -/

structure AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl :
    Type 1 where
  offset : Nat
  offset_at_least_two : 2 <= offset
  oldTrafficDataCoefficient : Q'
  newTrafficDebtCoefficient : Q'
  routeCoefficient : Q'
  oldTrafficDataCoefficient_nonnegative :
    (0 : Q') <= oldTrafficDataCoefficient
  newTrafficDebtCoefficient_nonnegative :
    (0 : Q') <= newTrafficDebtCoefficient
  routeCoefficient_nonnegative : (0 : Q') <= routeCoefficient
  oldTrafficData_le : forall scale : Nat,
    anchorTransportedBridgeOldTrafficDataDeficitMaximum scale <=
      oldTrafficDataCoefficient *
        invSqTerm offset offset_at_least_two scale
  newTrafficDebt_le : forall scale : Nat,
    anchorTransportedBridgeNewEndpointTrafficDebtMaximum scale <=
      newTrafficDebtCoefficient *
        invSqTerm offset offset_at_least_two scale
  route_le : forall scale : Nat,
    anchorTransportedBridgeRouteDeficitMaximum scale <=
      routeCoefficient * invSqTerm offset offset_at_least_two scale

def AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl.toTrafficControl
    (control :
      AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl) :
    AnchorCanonicalTransportedCapacityDebtTrafficInverseSquareControl where
  offset := control.offset
  offset_at_least_two := control.offset_at_least_two
  oldTrafficDataCoefficient := control.oldTrafficDataCoefficient
  newTrafficCoefficient := control.newTrafficDebtCoefficient
  routeCoefficient := control.routeCoefficient
  oldTrafficDataCoefficient_nonnegative :=
    control.oldTrafficDataCoefficient_nonnegative
  newTrafficCoefficient_nonnegative :=
    control.newTrafficDebtCoefficient_nonnegative
  routeCoefficient_nonnegative := control.routeCoefficient_nonnegative
  oldTrafficData_le := control.oldTrafficData_le
  newTraffic_le := fun scale =>
    Q'.le_trans' _ _ _
      (anchorTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
        scale)
      (control.newTrafficDebt_le scale)
  route_le := control.route_le

structure AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl :
    Type 1 where
  transport :
    AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
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

def AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTrafficRegionalControl
    (control :
      AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtTrafficRegionalInverseSquareControl where
  transport := control.transport.toTrafficControl
  oldNewCoefficient := control.oldNewCoefficient
  newOldCoefficient := control.newOldCoefficient
  newNewCoefficient := control.newNewCoefficient
  oldNewCoefficient_nonnegative := control.oldNewCoefficient_nonnegative
  newOldCoefficient_nonnegative := control.newOldCoefficient_nonnegative
  newNewCoefficient_nonnegative := control.newNewCoefficient_nonnegative
  oldNew_le := control.oldNew_le
  newOld_le := control.newOld_le
  newNew_le := control.newNew_le

def AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalControl
    (control :
      AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl) :
    AnchorCanonicalCapacityDebtInverseSquareControl :=
  control.toTrafficRegionalControl.toTotalControl

def anchorCanonicalCapacityDebtPersistenceOfExactTrafficInverseSquare
    (control :
      AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTrafficRegionalControl.toBridgeRegionalControl.toTotalDeficitTail
          tailAllowance <= (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence :=
  anchorCanonicalCapacityDebtPersistenceOfTrafficInverseSquare
    control.toTrafficRegionalControl tailAllowance tailAllowance_pos
    initial_closure

def anchorGeometricCompletedFamilyOfExactTrafficInverseSquare
    (control :
      AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget
          control.toTrafficRegionalControl.toBridgeRegionalControl.toTotalDeficitTail
          tailAllowance <= (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  anchorGeometricCompletedFamilyOfTrafficInverseSquare
    control.toTrafficRegionalControl tailAllowance tailAllowance_pos
    initial_closure

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.centralLowerExcitedSpinCubeOffRayResidualPathReverseForwardProduct_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.centralLowerExcitedSpinCubeOffRayResidualRoutedPathPairConditionalTransitionProductTerm_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.anchorTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.anchorTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.anchorTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.anchorTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.AnchorCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl.toTrafficControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.AnchorCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtNewTraffic.anchorGeometricCompletedFamilyOfExactTrafficInverseSquare
