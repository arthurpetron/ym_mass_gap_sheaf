/-
# Exact nonnegative new-traffic debt on the matched dynamic bridge

The traffic bridge measures entry of genuinely new endpoint pairs by a
two-sided absolute deficit.  The full transported-route debt is already the
exact sum of old and new traffic debt.  Shared routed-traffic nonnegativity
therefore contracts this symmetric deficit to the literal new-traffic debt,
with no factor two and no change of capacity denominator.

An inverse-square estimate on the exact new debt compiles into the six-leaf
traffic bridge and then the one total cutoff tail.  No estimate, physical-
scale uniformity, continuum theory, or Clay conclusion is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or declaration
marked noncomputable is used.
-/

import YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity

namespace YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtInverseSquareTail
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtRouteBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtShellFaces
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTrafficBridge
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalPairRecoding
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalSupportPointwiseVariationCompiler
open YMGap.Continuum.BF4PhysicalMatchedAFDynamicFamilyCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualConditionalCongestion
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualRoutedTrafficNonnegativity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SummableInverseSquare
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

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

/-! ## 1. The complementary matched load and debt are nonnegative -/

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
  apply listQSum_nonnegative_on
  intro pair _hpair
  exact residualRoutedPathPairConditionalTransitionProductTerm_nonnegative
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset)
    edge.1 edge.2 pair

theorem matchedEventualCapacityDebtFromLoadOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat)
    (edge : Nat × Nat) (load : Q')
    (hload : (0 : Q') <= load) :
    (0 : Q') <=
      matchedEventualCapacityDebtFromLoadOnPair
        trajectory transitionStart physicalScale cutoffOffset edge load := by
  unfold matchedEventualCapacityDebtFromLoadOnPair
  dsimp only
  by_cases hcapacity : (0 : Q') <
      HalfPow.half *
        centralPhysicalFiniteConditionalKernel
          (trajectory.nome physicalScale)
          (Q'.le_of_lt (trajectory.nome_pos physicalScale))
          (transitionStart physicalScale + cutoffOffset)
          0 edge.1 edge.2
  · rw [dif_pos hcapacity]
    unfold Q'.divPos
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _
        (Q'.le_of_lt
          (matchedEventualCanonicalSupportSharedFloor_pos
            trajectory transitionStart physicalScale))
        hload)
      (Q'.le_of_lt (Q'.recipPos_pos _ hcapacity))
  · rw [dif_neg hcapacity]
    exact Q'.le_refl' 0

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (edge : Nat × Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset edge :=
  matchedEventualCapacityDebtFromLoadOnPair_nonnegative
    trajectory transitionStart physicalScale (cutoffOffset + 1) edge
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair
      trajectory transitionStart physicalScale cutoffOffset edge)
    (matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge)

/-! ## 2. The symmetric new-traffic deficit is at most the exact debt -/

theorem matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) (pair : Nat × Nat) :
    matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair
        trajectory transitionStart physicalScale cutoffOffset pair <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair) := by
  let edge := matchedEventualCanonicalCurrentPairToNext
    trajectory transitionStart physicalScale cutoffOffset pair
  let oldDebt :=
    matchedEventualCanonicalTransportedBridgeOldEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let newDebt :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
      trajectory transitionStart physicalScale cutoffOffset edge
  let fullDebt := matchedEventualRoutedCapacityDebtOnPairForRouting
    trajectory transitionStart physicalScale (cutoffOffset + 1)
    (matchedEventualCanonicalTransportedRoutingAtNext
      trajectory transitionStart physicalScale cutoffOffset) edge
  have hsplit : fullDebt ≈ oldDebt + newDebt :=
    matchedEventualCanonicalTransportedBridgeCapacityDebtOnPair_eqv_old_add_new
      trajectory transitionStart physicalScale cutoffOffset edge
  have hnewNonnegative : (0 : Q') <= newDebt :=
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset edge
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

def matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) : Q' :=
  listQMaxZero
    (fun pair =>
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
        trajectory transitionStart physicalScale cutoffOffset
        (matchedEventualCanonicalCurrentPairToNext
          trajectory transitionStart physicalScale cutoffOffset pair))
    (matchedEventualCanonicalVacuumSectorPairs
      trajectory transitionStart physicalScale cutoffOffset)

theorem matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_nonnegative
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    (0 : Q') <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
  apply listQMaxZero_nonnegative
  intro pair
  exact
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
      trajectory transitionStart physicalScale cutoffOffset
      (matchedEventualCanonicalCurrentPairToNext
        trajectory transitionStart physicalScale cutoffOffset pair)

theorem matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale cutoffOffset : Nat) :
    matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset := by
  unfold matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum
  apply listQMaxZero_le_of_member_bound_local
  · exact
      matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum_nonnegative
        trajectory transitionStart physicalScale cutoffOffset
  · intro pair hpair
    exact Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt
        trajectory transitionStart physicalScale cutoffOffset pair)
      (le_listQMaxZero_of_mem
        (fun item =>
          matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair
            trajectory transitionStart physicalScale cutoffOffset
            (matchedEventualCanonicalCurrentPairToNext
              trajectory transitionStart physicalScale cutoffOffset item))
        (matchedEventualCanonicalVacuumSectorPairs
          trajectory transitionStart physicalScale cutoffOffset) hpair)

/-! ## 3. Exact-debt estimates compile to the six-leaf traffic control -/

structure MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
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
  oldTrafficData_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeOldTrafficDataDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldTrafficDataCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  newTrafficDebt_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newTrafficDebtCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset
  route_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalTransportedBridgeRouteDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      routeCoefficient *
        invSqTerm offset offset_at_least_two cutoffOffset

def MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl.toTrafficControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalTransportedCapacityDebtTrafficInverseSquareControl
      trajectory transitionStart physicalScale where
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
  newTraffic_le := fun cutoffOffset =>
    Q'.le_trans' _ _ _
      (matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
        trajectory transitionStart physicalScale cutoffOffset)
      (control.newTrafficDebt_le cutoffOffset)
  route_le := control.route_le

structure MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    (trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing)
    (transitionStart : Nat -> Nat)
    (physicalScale : Nat) : Type 1 where
  transport :
    MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl
      trajectory transitionStart physicalScale
  oldNewCoefficient : Q'
  newOldCoefficient : Q'
  newNewCoefficient : Q'
  oldNewCoefficient_nonnegative : (0 : Q') <= oldNewCoefficient
  newOldCoefficient_nonnegative : (0 : Q') <= newOldCoefficient
  newNewCoefficient_nonnegative : (0 : Q') <= newNewCoefficient
  oldNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalOldNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      oldNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newOld_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewOldReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newOldCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset
  newNew_le : forall cutoffOffset : Nat,
    matchedEventualCanonicalNewNewReturnCapacityDebtDeficitMaximum
        trajectory transitionStart physicalScale cutoffOffset <=
      newNewCoefficient *
        invSqTerm transport.offset
          transport.offset_at_least_two cutoffOffset

def MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTrafficRegionalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTrafficRegionalInverseSquareControl
      trajectory transitionStart physicalScale where
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

def MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalControl
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtInverseSquareControl
      trajectory transitionStart physicalScale :=
  control.toTrafficRegionalControl.toTotalControl

def MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalDeficitTail
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {trajectory :
      MatchedPhysicalDynamicScalarTrajectory family law spacing}
    {transitionStart : Nat -> Nat}
    {physicalScale : Nat}
    (control :
      MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl
        trajectory transitionStart physicalScale) :
    MatchedEventualCanonicalCapacityDebtTotalDeficitTail
      trajectory transitionStart physicalScale :=
  control.toTotalControl.toTotalDeficitTail

end YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficLoadOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.matchedEventualCanonicalTransportedBridgeNewEndpointTrafficDebtOnPair_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.matchedEventualCanonicalTransportedBridgeNewTrafficDeficitOnPair_le_exactDebt
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.matchedEventualCanonicalTransportedBridgeNewTrafficDeficitMaximum_le_exactDebtMaximum
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.MatchedEventualCanonicalTransportedCapacityDebtExactTrafficInverseSquareControl.toTrafficControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalControl
#print axioms
  YMGap.Continuum.BF4PhysicalMatchedAFDynamicExplicitRayEventualCanonicalCorrelatedCapacityDebtNewTraffic.MatchedEventualCanonicalCapacityDebtExactTrafficRegionalInverseSquareControl.toTotalDeficitTail
