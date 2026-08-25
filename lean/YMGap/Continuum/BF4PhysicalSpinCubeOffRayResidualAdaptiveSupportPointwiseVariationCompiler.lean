/-
# Pointwise dynamic-carrier compilers for the support-aware BF4 debt

The preceding primitive two-lane compiler asks for summable variation of a
located load maximum and of a located supported-kernel minimum, plus a uniform
positive floor for the latter.  Those aggregate extrema should not be treated
as opaque analytic inputs.

This module reduces them to literal pointwise estimates on consecutive finite
carriers.  A dynamic maximum is controlled by recoding every current item into
the next carrier and every next item back into the current carrier, with the
appropriate one-sided value estimates.  A dynamic minimum uses the reversed
one-sided estimates.  A pointwise positive lower bound, including the unit
fallback used by `listPositiveMinOne`, supplies the uniform minimum floor.

At the BF4 specialization the values are exactly the routed transition-product
load and the support-aware conditional-kernel candidate, on the exact finite
vacuum-sector pair lists and for one common routing sequence.  Thus no
observable or carrier surrogate enters the compiler.

No recoding, pointwise variation, uniform kernel floor, total debt budget, or
initial slack is inhabited here.  The fixed anchor is not the physical AF
trajectory, and no thermodynamic, continuum, or Clay conclusion is asserted.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RG.StableDynamics
open YMGap.Continuum.BF4PhysicalAnchorDynamicRayCapacityCompiler
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveFiniteCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveRouting
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportMarginProxy
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Generic dynamic finite-maximum recoding -/

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

/-- Summable pointwise recoding data sufficient to control a located maximum
on a changing finite carrier.  The two maps are explicit computational data;
the estimates are oriented exactly as maximum comparison requires. -/
structure DynamicFiniteMaximumVariation
    {State : Type}
    (value : Nat -> State -> Q')
    (carrier : Nat -> List State) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  value_nonnegative : forall scale state, (0 : Q') <= value scale state
  currentToNext : Nat -> State -> State
  currentToNext_mem : forall scale state,
    state ∈ carrier scale -> currentToNext scale state ∈ carrier (scale + 1)
  current_le_next : forall scale state,
    state ∈ carrier scale ->
      value scale state <=
        value (scale + 1) (currentToNext scale state) + variation scale
  nextToCurrent : Nat -> State -> State
  nextToCurrent_mem : forall scale state,
    state ∈ carrier (scale + 1) -> nextToCurrent scale state ∈ carrier scale
  next_le_current : forall scale state,
    state ∈ carrier (scale + 1) ->
      value (scale + 1) state <=
        value scale (nextToCurrent scale state) + variation scale

namespace DynamicFiniteMaximumVariation

/-- The two explicit carrier recodings compile to summable variation of the
located maximum itself. -/
def toSummableRationalStepVariation
    {State : Type}
    {value : Nat -> State -> Q'}
    {carrier : Nat -> List State}
    (data : DynamicFiniteMaximumVariation value carrier) :
    SummableRationalStepVariation
      (fun scale => listQMaxZero (value scale) (carrier scale)) where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  stepBound := fun scale => by
    have currentMaximum_nonnegative : (0 : Q') <=
        listQMaxZero (value scale) (carrier scale) :=
      listQMaxZero_nonnegative _ (data.value_nonnegative scale) _
    have nextMaximum_nonnegative : (0 : Q') <=
        listQMaxZero (value (scale + 1)) (carrier (scale + 1)) :=
      listQMaxZero_nonnegative _ (data.value_nonnegative (scale + 1)) _
    constructor
    · apply listQMaxZero_le_of_member_bound_local
      · exact Q'.zero_le_add _ _ currentMaximum_nonnegative
          (data.variation_nonnegative scale)
      · intro state hstate
        exact Q'.le_trans' _ _ _
          (data.next_le_current scale state hstate)
          (Q'.add_le_add_right _ _ _
            (le_listQMaxZero_of_mem
              (value scale) (carrier scale)
              (data.nextToCurrent_mem scale state hstate)))
    · apply listQMaxZero_le_of_member_bound_local
      · exact Q'.zero_le_add _ _ nextMaximum_nonnegative
          (data.variation_nonnegative scale)
      · intro state hstate
        exact Q'.le_trans' _ _ _
          (data.current_le_next scale state hstate)
          (Q'.add_le_add_right _ _ _
            (le_listQMaxZero_of_mem
              (value (scale + 1)) (carrier (scale + 1))
              (data.currentToNext_mem scale state hstate)))

end DynamicFiniteMaximumVariation

/-! ## 2. Generic dynamic finite-minimum recoding and floor -/

private theorem listPositiveMinOne_le_one_local
    {State : Type} (value : State -> Q') :
    forall states : List State,
      listPositiveMinOne value states <= (1 : Q')
  | [] => Q'.le_refl' 1
  | _head :: tail =>
      Q'.le_trans' _ _ _
        (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value tail)

private theorem listPositiveMinOne_step_le_of_recode_local
    {State : Type}
    (leftValue rightValue : State -> Q')
    (rightStates : List State)
    (variation : Q') (variation_nonnegative : (0 : Q') <= variation)
    (recode : State -> State) :
    forall leftStates : List State,
      (forall state, state ∈ leftStates -> recode state ∈ rightStates) ->
      (forall state, state ∈ leftStates ->
        rightValue (recode state) <= leftValue state + variation) ->
      listPositiveMinOne rightValue rightStates <=
        listPositiveMinOne leftValue leftStates + variation
  | [], _, _ =>
      Q'.le_trans' _ _ _
        (listPositiveMinOne_le_one_local rightValue rightStates)
        (Q'.add_le_self_of_nonneg 1 variation variation_nonnegative)
  | head :: tail, hmem, hbound => by
      change listPositiveMinOne rightValue rightStates <=
        Q'.min' (leftValue head) (listPositiveMinOne leftValue tail) +
          variation
      unfold Q'.min'
      by_cases hle : leftValue head <= listPositiveMinOne leftValue tail
      · rw [if_pos hle]
        exact Q'.le_trans' _ _ _
          (listPositiveMinOne_le_of_mem rightValue rightStates
            (recode head) (hmem head List.mem_cons_self))
          (hbound head List.mem_cons_self)
      · rw [if_neg hle]
        exact listPositiveMinOne_step_le_of_recode_local
          leftValue rightValue rightStates variation variation_nonnegative
          recode tail
          (fun state hstate =>
            hmem state (List.mem_cons_of_mem head hstate))
          (fun state hstate =>
            hbound state (List.mem_cons_of_mem head hstate))

/-- Summable pointwise recoding data sufficient to control a located minimum
on a changing finite carrier.  The estimates have the dual orientation to the
maximum compiler. -/
structure DynamicFiniteMinimumVariation
    {State : Type}
    (value : Nat -> State -> Q')
    (carrier : Nat -> List State) : Type 1 where
  variation : Nat -> Q'
  variation_nonnegative : forall scale, (0 : Q') <= variation scale
  tailControl : AntitoneTailControl variation
  currentToNext : Nat -> State -> State
  currentToNext_mem : forall scale state,
    state ∈ carrier scale -> currentToNext scale state ∈ carrier (scale + 1)
  next_le_current : forall scale state,
    state ∈ carrier scale ->
      value (scale + 1) (currentToNext scale state) <=
        value scale state + variation scale
  nextToCurrent : Nat -> State -> State
  nextToCurrent_mem : forall scale state,
    state ∈ carrier (scale + 1) -> nextToCurrent scale state ∈ carrier scale
  current_le_next : forall scale state,
    state ∈ carrier (scale + 1) ->
      value scale (nextToCurrent scale state) <=
        value (scale + 1) state + variation scale

namespace DynamicFiniteMinimumVariation

/-- The two explicit carrier recodings compile to summable variation of the
located unit-seeded minimum itself. -/
def toSummableRationalStepVariation
    {State : Type}
    {value : Nat -> State -> Q'}
    {carrier : Nat -> List State}
    (data : DynamicFiniteMinimumVariation value carrier) :
    SummableRationalStepVariation
      (fun scale => listPositiveMinOne (value scale) (carrier scale)) where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := data.tailControl
  stepBound := fun scale =>
    ⟨listPositiveMinOne_step_le_of_recode_local
        (value scale) (value (scale + 1)) (carrier (scale + 1))
        (data.variation scale) (data.variation_nonnegative scale)
        (data.currentToNext scale) (carrier scale)
        (data.currentToNext_mem scale) (data.next_le_current scale),
      listPositiveMinOne_step_le_of_recode_local
        (value (scale + 1)) (value scale) (carrier scale)
        (data.variation scale) (data.variation_nonnegative scale)
        (data.nextToCurrent scale) (carrier (scale + 1))
        (data.nextToCurrent_mem scale) (data.current_le_next scale)⟩

end DynamicFiniteMinimumVariation

private theorem listPositiveMinOne_lower_bound_local
    {State : Type} (value : State -> Q') (candidate : Q') :
    forall states : List State,
      candidate <= 1 ->
      (forall state, state ∈ states -> candidate <= value state) ->
      candidate <= listPositiveMinOne value states
  | [], hunit, _ => hunit
  | head :: tail, hunit, hall => by
      unfold listPositiveMinOne Q'.min'
      by_cases hle : value head <= listPositiveMinOne value tail
      · rw [if_pos hle]
        exact hall head List.mem_cons_self
      · rw [if_neg hle]
        exact listPositiveMinOne_lower_bound_local value candidate tail hunit
          (fun state hstate =>
            hall state (List.mem_cons_of_mem head hstate))

/-- A pointwise lower bound, including the unit fallback, is an explicit
uniform floor for every dynamic located minimum. -/
structure DynamicFiniteMinimumFloor
    {State : Type}
    (value : Nat -> State -> Q')
    (carrier : Nat -> List State) : Type 1 where
  floor : Q'
  floor_pos : (0 : Q') < floor
  floor_le_one : floor <= (1 : Q')
  floor_le_value : forall scale state,
    state ∈ carrier scale -> floor <= value scale state

theorem DynamicFiniteMinimumFloor.le_minimum
    {State : Type}
    {value : Nat -> State -> Q'}
    {carrier : Nat -> List State}
    (data : DynamicFiniteMinimumFloor value carrier)
    (scale : Nat) :
    data.floor <= listPositiveMinOne (value scale) (carrier scale) :=
  listPositiveMinOne_lower_bound_local
    (value scale) data.floor (carrier scale)
    data.floor_le_one (data.floor_le_value scale)

/-! ## 3. Exact BF4 pointwise specializations -/

private def anchorVacuumSectorPairs (scale : Nat) : List (Nat × Nat) :=
  centralPhysicalFiniteVacuumSectorPairs
    anchorCoupling (Q'.le_of_lt anchorCoupling_pos) scale 0

private def anchorRoutedLoadOnPair
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadOnPair
    (routing scale) pair

private def anchorSupportedKernelCandidateOnPair
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (scale : Nat) (pair : Nat × Nat) : Q' :=
  centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelCandidate
    (routing scale) pair.1 pair.2

/-- Pointwise recoding input for the exact routed-load maximum. -/
abbrev AnchorAdaptiveRoutedLoadMaximumVariation
    (routing : AnchorAdaptivePositiveRoutingSequence) : Type 1 :=
  DynamicFiniteMaximumVariation
    (anchorRoutedLoadOnPair routing) anchorVacuumSectorPairs

/-- Pointwise recoding input for the exact supported-kernel minimum. -/
abbrev AnchorAdaptiveSupportedKernelMinimumVariation
    (routing : AnchorAdaptivePositiveRoutingSequence) : Type 1 :=
  DynamicFiniteMinimumVariation
    (anchorSupportedKernelCandidateOnPair routing) anchorVacuumSectorPairs

/-- Pointwise noncollapse input for the exact supported-kernel minimum. -/
abbrev AnchorAdaptiveSupportedKernelMinimumFloor
    (routing : AnchorAdaptivePositiveRoutingSequence) : Type 1 :=
  DynamicFiniteMinimumFloor
    (anchorSupportedKernelCandidateOnPair routing) anchorVacuumSectorPairs

/-- Compile the exact routed-load maximum variation from its two pointwise
carrier recodings. -/
def anchorAdaptiveRoutedLoadMaximumVariationOfPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveRoutedLoadMaximumVariation routing) :
    SummableRationalStepVariation
      (fun scale =>
        centralLowerExcitedSpinCubeOffRayResidualRoutedConditionalTransitionProductLoadMaximum
          (routing scale)) := by
  change SummableRationalStepVariation
    (fun scale => listQMaxZero
      (anchorRoutedLoadOnPair routing scale)
      (anchorVacuumSectorPairs scale))
  exact data.toSummableRationalStepVariation

/-- Adding the exact positive unit seed to the routed maximum preserves the
compiled variation and gives the load-denominator lane required downstream. -/
def anchorAdaptiveRoutedLoadDenominatorVariationOfPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveRoutedLoadMaximumVariation routing) :
    SummableRationalStepVariation
      (anchorAdaptiveRoutedLoadDenominator routing) := by
  let unitVariation :=
    SummableRationalStepVariation.ofPointwiseEqvConstant
      (fun _scale => (1 : Q')) 1 (fun _scale => Q'.eqv_refl 1)
  let maximumVariation :=
    anchorAdaptiveRoutedLoadMaximumVariationOfPointwise routing data
  exact add unitVariation maximumVariation

/-- Compile the exact support-aware conditional-kernel minimum variation from
its two pointwise carrier recodings. -/
def anchorAdaptiveSupportedKernelMinimumVariationOfPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveSupportedKernelMinimumVariation routing) :
    SummableRationalStepVariation
      (fun scale =>
        centralLowerExcitedSpinCubeOffRayResidualRoutedSupportedConditionalKernelFloor
          (routing scale)) := by
  change SummableRationalStepVariation
    (fun scale => listPositiveMinOne
      (anchorSupportedKernelCandidateOnPair routing scale)
      (anchorVacuumSectorPairs scale))
  exact data.toSummableRationalStepVariation

/-- Scaling the compiled support minimum by the literal half factor gives the
non-inverted kernel-numerator variation required by the primitive join. -/
def anchorAdaptiveSupportedKernelNumeratorVariationOfPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveSupportedKernelMinimumVariation routing) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportedKernelNumerator routing) := by
  exact scale
    (anchorAdaptiveSupportedKernelMinimumVariationOfPointwise routing data)
    HalfPow.half (by decide)

/-- The pointwise support floor, scaled by the same literal half factor as the
kernel numerator. -/
def anchorAdaptiveSupportedKernelNumeratorFloor
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveSupportedKernelMinimumFloor routing) : Q' :=
  HalfPow.half * data.floor

theorem anchorAdaptiveSupportedKernelNumeratorFloor_pos
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveSupportedKernelMinimumFloor routing) :
    (0 : Q') < anchorAdaptiveSupportedKernelNumeratorFloor routing data :=
  Q'.mul_pos (by decide) data.floor_pos

theorem anchorAdaptiveSupportedKernelNumeratorFloor_le
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (data : AnchorAdaptiveSupportedKernelMinimumFloor routing)
    (scale : Nat) :
    anchorAdaptiveSupportedKernelNumeratorFloor routing data <=
      anchorAdaptiveSupportedKernelNumerator routing scale := by
  unfold anchorAdaptiveSupportedKernelNumeratorFloor
    anchorAdaptiveSupportedKernelNumerator
  exact Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half
    (data.le_minimum scale) (by decide)

/-! ## 4. The observable-connected pointwise join -/

/-- Three concurrently provable pointwise certificates -- load recoding,
kernel recoding, and kernel noncollapse -- compile into summable variation of
the existing exact normalized debt. -/
def anchorAdaptiveSupportCapacityDebtVariationOfPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (loadData : AnchorAdaptiveRoutedLoadMaximumVariation routing)
    (kernelVariationData :
      AnchorAdaptiveSupportedKernelMinimumVariation routing)
    (kernelFloorData : AnchorAdaptiveSupportedKernelMinimumFloor routing) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt routing) :=
  anchorAdaptiveSupportCapacityDebtVariationOfPrimitiveComponents
    routing
    (anchorAdaptiveRoutedLoadDenominatorVariationOfPointwise routing loadData)
    (anchorAdaptiveSupportedKernelNumeratorVariationOfPointwise
      routing kernelVariationData)
    (anchorAdaptiveSupportedKernelNumeratorFloor routing kernelFloorData)
    (anchorAdaptiveSupportedKernelNumeratorFloor_pos routing kernelFloorData)
    (anchorAdaptiveSupportedKernelNumeratorFloor_le routing kernelFloorData)

/-- End-to-end fixed-anchor compiler from the pointwise dynamic-carrier
frontier, followed by the unchanged total-budget and initial-slack check. -/
def anchorAdaptiveSupportCapacityDebtVariationFromPointwise
    (routing : AnchorAdaptivePositiveRoutingSequence)
    (loadData : AnchorAdaptiveRoutedLoadMaximumVariation routing)
    (kernelVariationData :
      AnchorAdaptiveSupportedKernelMinimumVariation routing)
    (kernelFloorData : AnchorAdaptiveSupportedKernelMinimumFloor routing)
    (budget : Q')
    (budget_pos : (0 : Q') < budget)
    (budget_from_zero :
      (anchorAdaptiveSupportCapacityDebtVariationOfPointwise
        routing loadData kernelVariationData kernelFloorData).tailControl.tailRate
          budget = 0)
    (initial_closure :
      anchorAdaptiveSupportCapacityDebt routing 0 + budget <= (1 : Q')) :
    AnchorAdaptiveFiniteCapacityDebtVariation :=
  anchorAdaptiveSupportCapacityDebtVariation
    routing
    (anchorAdaptiveSupportCapacityDebtVariationOfPointwise
      routing loadData kernelVariationData kernelFloorData)
    budget budget_pos budget_from_zero initial_closure

/-- Canonical loop-erased routing specialization of the pointwise compiler.
It removes routing construction, but inhabits none of the three analytic
pointwise certificates. -/
def anchorCanonicalSupportCapacityDebtVariationOfPointwise
    (loadData : AnchorAdaptiveRoutedLoadMaximumVariation
      anchorCanonicalPositiveRoutingSequence)
    (kernelVariationData : AnchorAdaptiveSupportedKernelMinimumVariation
      anchorCanonicalPositiveRoutingSequence)
    (kernelFloorData : AnchorAdaptiveSupportedKernelMinimumFloor
      anchorCanonicalPositiveRoutingSequence) :
    SummableRationalStepVariation
      (anchorAdaptiveSupportCapacityDebt
        anchorCanonicalPositiveRoutingSequence) :=
  anchorAdaptiveSupportCapacityDebtVariationOfPointwise
    anchorCanonicalPositiveRoutingSequence
    loadData kernelVariationData kernelFloorData

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.DynamicFiniteMaximumVariation.toSummableRationalStepVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.DynamicFiniteMinimumVariation.toSummableRationalStepVariation
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.DynamicFiniteMinimumFloor.le_minimum
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorAdaptiveRoutedLoadDenominatorVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorAdaptiveSupportedKernelNumeratorVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorAdaptiveSupportedKernelNumeratorFloor_le
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorAdaptiveSupportCapacityDebtVariationOfPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorAdaptiveSupportCapacityDebtVariationFromPointwise
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportPointwiseVariationCompiler.anchorCanonicalSupportCapacityDebtVariationOfPointwise
