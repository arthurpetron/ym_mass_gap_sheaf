/-
# Exact three-block pattern balance and bounded leakage

Strict fiber locality forces equality of all eight three-bit pattern masses.
For a genuine RG step those cell laws may differ.  This module gives the
constructive alternative: every positive exact coupling satisfies an exact
incoming/outgoing conservation law at each pattern, and the signed cell-mass
defect is bounded by the corresponding cross-pattern leakage.

This is the finite algebra needed to turn a physically derived local leakage
estimate into a per-scale defect.  No leakage constant is postulated here;
the residual is to derive it from the exact character/fusion amplitudes of a
concrete physical block kernel.
-/

import YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

namespace YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic Boolean-event flow decomposition -/

theorem listQSum_bool_partition {A : Type}
    (weight : A → Q') (states : List A) (event : A → Bool) :
    listQSum weight states ≈
      listQSum (fun state => if event state then weight state else 0) states +
      listQSum (fun state => if event state then 0 else weight state) states := by
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then weight state else 0) +
          (if event state then 0 else weight state)) states) _ ?_ ?_
  · apply listQSum_congr_on
    intro state _
    cases hevent : event state
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' (weight state)))
    · simp only [if_true]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' (weight state)))
  exact listQSum_add _ _ states

def finiteEventMatchedJointMass {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q') : Q' :=
  listQSum
    (fun source =>
      if sourceEvent source then
        listQSum
          (fun target => if targetEvent target then
            jointMass source target else 0) targetStates
      else 0) sourceStates

/-- Mass leaving the selected source event and landing outside the selected
target event. -/
def finiteEventOutgoingLeakage {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q') : Q' :=
  listQSum
    (fun source =>
      if sourceEvent source then
        listQSum
          (fun target => if targetEvent target then 0
            else jointMass source target) targetStates
      else 0) sourceStates

/-- Mass entering the selected target event from outside the selected source
event. -/
def finiteEventIncomingLeakage {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q') : Q' :=
  listQSum
    (fun source =>
      if sourceEvent source then 0
      else
        listQSum
          (fun target => if targetEvent target then
            jointMass source target else 0) targetStates)
    sourceStates

theorem finiteEventOutgoingLeakage_nonnegative {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (hjoint : ∀ source target, (0 : Q') ≤ jointMass source target) :
    (0 : Q') ≤ finiteEventOutgoingLeakage
      sourceStates targetStates sourceEvent targetEvent jointMass := by
  unfold finiteEventOutgoingLeakage
  apply listQSum_nonnegative_on
  intro source _
  cases hsource : sourceEvent source
  · simp only [Bool.false_eq_true, if_false]
    exact Q'.le_refl' 0
  · simp only [if_true]
    apply listQSum_nonnegative_on
    intro target _
    cases htarget : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact hjoint source target
    · simp only [if_true]
      exact Q'.le_refl' 0

theorem finiteEventIncomingLeakage_nonnegative {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (hjoint : ∀ source target, (0 : Q') ≤ jointMass source target) :
    (0 : Q') ≤ finiteEventIncomingLeakage
      sourceStates targetStates sourceEvent targetEvent jointMass := by
  unfold finiteEventIncomingLeakage
  apply listQSum_nonnegative_on
  intro source _
  cases hsource : sourceEvent source
  · simp only [Bool.false_eq_true, if_false]
    apply listQSum_nonnegative_on
    intro target _
    cases htarget : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.le_refl' 0
    · simp only [if_true]
      exact hjoint source target
  · simp only [if_true]
    exact Q'.le_refl' 0

theorem finiteEvent_source_mass_decomposition
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceMass sourceStates targetMass targetStates jointMass) :
    finiteEventMass sourceMass sourceStates sourceEvent ≈
      finiteEventMatchedJointMass sourceStates targetStates
          sourceEvent targetEvent jointMass +
        finiteEventOutgoingLeakage sourceStates targetStates
          sourceEvent targetEvent jointMass := by
  unfold finiteEventMass finiteEventMatchedJointMass
    finiteEventOutgoingLeakage
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (if sourceEvent source then
          listQSum
            (fun target => if targetEvent target then
              jointMass source target else 0) targetStates
        else 0) +
        (if sourceEvent source then
          listQSum
            (fun target => if targetEvent target then 0
              else jointMass source target) targetStates
        else 0)) sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    cases hsource : sourceEvent source
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' 0))
    · simp only [if_true]
      refine Q'.eqv_trans _
        (listQSum (jointMass source) targetStates) _
        (Q'.eqv_symm (coupling.source_marginal source)) ?_
      exact listQSum_bool_partition
        (jointMass source) targetStates targetEvent
  exact listQSum_add _ _ sourceStates

theorem finiteEvent_target_mass_decomposition
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceMass sourceStates targetMass targetStates jointMass) :
    finiteEventMass targetMass targetStates targetEvent ≈
      finiteEventMatchedJointMass sourceStates targetStates
          sourceEvent targetEvent jointMass +
        finiteEventIncomingLeakage sourceStates targetStates
          sourceEvent targetEvent jointMass := by
  let targetSelected := fun target source =>
    if targetEvent target then jointMass source target else 0
  have htarget :
      finiteEventMass targetMass targetStates targetEvent ≈
        listQSum
          (fun target => listQSum (targetSelected target) sourceStates)
          targetStates := by
    unfold finiteEventMass
    apply listQSum_congr_on
    intro target _
    cases htargetEvent : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      unfold targetSelected
      simp only [htargetEvent, Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (listQSum_zero sourceStates)
    · simp only [if_true]
      unfold targetSelected
      simp only [htargetEvent, if_true]
      exact Q'.eqv_symm (coupling.target_marginal target)
  refine Q'.eqv_trans _
    (listQSum
      (fun target => listQSum (targetSelected target) sourceStates)
      targetStates) _ htarget ?_
  refine Q'.eqv_trans _
    (listQSum
      (fun source => listQSum
        (fun target => targetSelected target source) targetStates)
      sourceStates) _
    (Q'.eqv_symm
      (listQSum_swap targetSelected targetStates sourceStates)) ?_
  unfold finiteEventMatchedJointMass finiteEventIncomingLeakage
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        (if sourceEvent source then
          listQSum
            (fun target => if targetEvent target then
              jointMass source target else 0) targetStates
        else 0) +
        (if sourceEvent source then 0
        else
          listQSum
            (fun target => if targetEvent target then
              jointMass source target else 0) targetStates))
      sourceStates) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    cases hsourceEvent : sourceEvent source
    · simp only [Bool.false_eq_true, if_false]
      unfold targetSelected
      refine Q'.eqv_trans _
        (listQSum
          (fun target => if targetEvent target then
            jointMass source target else 0) targetStates) _ ?_ ?_
      · exact Q'.eqv_refl _
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.zero_add' _))
    · simp only [if_true]
      unfold targetSelected
      refine Q'.eqv_trans _
        (listQSum
          (fun target => if targetEvent target then
            jointMass source target else 0) targetStates) _ ?_ ?_
      · exact Q'.eqv_refl _
      exact Q'.eqv_symm (Q'.eqv_of_eq (Q'.add_zero' _))
  exact listQSum_add _ _ sourceStates

private theorem add_sub_left_cancel_eqv (base extra : Q') :
    (base + extra) + -base ≈ extra := by
  refine Q'.eqv_trans _ (base + (extra + -base)) _
    (Q'.add_assoc_eqv base extra (-base)) ?_
  refine Q'.eqv_trans _ (base + (-base + extra)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl base)
      (Q'.add_comm_eqv extra (-base))) ?_
  refine Q'.eqv_trans _ ((base + -base) + extra) _
    (Q'.eqv_symm (Q'.add_assoc_eqv base (-base) extra)) ?_
  refine Q'.eqv_trans _ ((0 : Q') + extra) _
    (Q'.add_eqv_congr' (Q'.add_neg_self_eqv base)
      (Q'.eqv_refl extra)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' extra)

/-- Exact conservation across a selected Boolean cell. -/
theorem finiteEvent_leakage_balance
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceMass sourceStates targetMass targetStates jointMass) :
    finiteEventMass targetMass targetStates targetEvent +
        finiteEventOutgoingLeakage sourceStates targetStates
          sourceEvent targetEvent jointMass ≈
      finiteEventMass sourceMass sourceStates sourceEvent +
        finiteEventIncomingLeakage sourceStates targetStates
          sourceEvent targetEvent jointMass := by
  let matched := finiteEventMatchedJointMass sourceStates targetStates
    sourceEvent targetEvent jointMass
  let outgoing := finiteEventOutgoingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  let incoming := finiteEventIncomingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  have hsource : finiteEventMass sourceMass sourceStates sourceEvent ≈
      matched + outgoing :=
    finiteEvent_source_mass_decomposition sourceMass sourceStates
      targetMass targetStates sourceEvent targetEvent jointMass coupling
  have htarget : finiteEventMass targetMass targetStates targetEvent ≈
      matched + incoming :=
    finiteEvent_target_mass_decomposition sourceMass sourceStates
      targetMass targetStates sourceEvent targetEvent jointMass coupling
  refine Q'.eqv_trans _ ((matched + incoming) + outgoing) _
    (Q'.add_eqv_congr' htarget (Q'.eqv_refl outgoing)) ?_
  refine Q'.eqv_trans _ (matched + (incoming + outgoing)) _
    (Q'.add_assoc_eqv matched incoming outgoing) ?_
  refine Q'.eqv_trans _ (matched + (outgoing + incoming)) _
    (Q'.add_eqv_congr' (Q'.eqv_refl matched)
      (Q'.add_comm_eqv incoming outgoing)) ?_
  refine Q'.eqv_trans _ ((matched + outgoing) + incoming) _
    (Q'.eqv_symm (Q'.add_assoc_eqv matched outgoing incoming)) ?_
  exact Q'.add_eqv_congr' (Q'.eqv_symm hsource)
    (Q'.eqv_refl incoming)

/-- Target cell excess is no larger than incoming cross-cell leakage. -/
theorem finiteEvent_target_excess_le_incomingLeakage
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceMass sourceStates targetMass targetStates jointMass) :
    finiteEventMass targetMass targetStates targetEvent +
        -finiteEventMass sourceMass sourceStates sourceEvent ≤
      finiteEventIncomingLeakage sourceStates targetStates
        sourceEvent targetEvent jointMass := by
  let sourceValue := finiteEventMass sourceMass sourceStates sourceEvent
  let targetValue := finiteEventMass targetMass targetStates targetEvent
  let outgoing := finiteEventOutgoingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  let incoming := finiteEventIncomingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  have houtgoing0 : (0 : Q') ≤ outgoing :=
    finiteEventOutgoingLeakage_nonnegative sourceStates targetStates
      sourceEvent targetEvent jointMass coupling.nonnegative
  have htargetStep : targetValue ≤ targetValue + outgoing :=
    Q'.add_le_self_of_nonneg targetValue outgoing houtgoing0
  have hbalance : targetValue + outgoing ≈ sourceValue + incoming :=
    finiteEvent_leakage_balance sourceMass sourceStates targetMass
      targetStates sourceEvent targetEvent jointMass coupling
  have htargetBound : targetValue ≤ sourceValue + incoming :=
    Q'.le_trans' _ (targetValue + outgoing) _ htargetStep
      (Q'.le_of_eqv hbalance)
  have hshift := Q'.add_le_add_right targetValue
    (sourceValue + incoming) (-sourceValue) htargetBound
  exact Q'.le_trans' _ ((sourceValue + incoming) + -sourceValue) _
    hshift (Q'.le_of_eqv (add_sub_left_cancel_eqv sourceValue incoming))

/-- Source cell excess is no larger than outgoing cross-cell leakage. -/
theorem finiteEvent_source_excess_le_outgoingLeakage
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceMass sourceStates targetMass targetStates jointMass) :
    finiteEventMass sourceMass sourceStates sourceEvent +
        -finiteEventMass targetMass targetStates targetEvent ≤
      finiteEventOutgoingLeakage sourceStates targetStates
        sourceEvent targetEvent jointMass := by
  let sourceValue := finiteEventMass sourceMass sourceStates sourceEvent
  let targetValue := finiteEventMass targetMass targetStates targetEvent
  let outgoing := finiteEventOutgoingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  let incoming := finiteEventIncomingLeakage sourceStates targetStates
    sourceEvent targetEvent jointMass
  have hincoming0 : (0 : Q') ≤ incoming :=
    finiteEventIncomingLeakage_nonnegative sourceStates targetStates
      sourceEvent targetEvent jointMass coupling.nonnegative
  have hsourceStep : sourceValue ≤ sourceValue + incoming :=
    Q'.add_le_self_of_nonneg sourceValue incoming hincoming0
  have hbalance : targetValue + outgoing ≈ sourceValue + incoming :=
    finiteEvent_leakage_balance sourceMass sourceStates targetMass
      targetStates sourceEvent targetEvent jointMass coupling
  have hsourceBound : sourceValue ≤ targetValue + outgoing :=
    Q'.le_trans' _ (sourceValue + incoming) _ hsourceStep
      (Q'.le_of_eqv (Q'.eqv_symm hbalance))
  have hshift := Q'.add_le_add_right sourceValue
    (targetValue + outgoing) (-targetValue) hsourceBound
  exact Q'.le_trans' _ ((targetValue + outgoing) + -targetValue) _
    hshift (Q'.le_of_eqv (add_sub_left_cancel_eqv targetValue outgoing))

/-! ## 2. The eight-cell three-block specialization -/

def threeBlockPatternIncomingLeakage {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (pattern : ThreeBlockPattern) : Q' :=
  finiteEventIncomingLeakage sourceLaw.states targetLaw.states
    (threeBlockPatternEvent sourceLaw pattern)
    (threeBlockPatternEvent targetLaw pattern) jointMass

def threeBlockPatternOutgoingLeakage {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (pattern : ThreeBlockPattern) : Q' :=
  finiteEventOutgoingLeakage sourceLaw.states targetLaw.states
    (threeBlockPatternEvent sourceLaw pattern)
    (threeBlockPatternEvent targetLaw pattern) jointMass

theorem threeBlockPattern_target_excess_le_incomingLeakage
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states jointMass)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass targetLaw pattern +
        -threeBlockPatternMass sourceLaw pattern ≤
      threeBlockPatternIncomingLeakage sourceLaw targetLaw jointMass pattern := by
  have hbound := finiteEvent_target_excess_le_incomingLeakage
    sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states
    (threeBlockPatternEvent sourceLaw pattern)
    (threeBlockPatternEvent targetLaw pattern) jointMass coupling
  unfold threeBlockPatternIncomingLeakage
  refine Q'.le_trans' _
    (finiteEventMass targetLaw.mass targetLaw.states
        (threeBlockPatternEvent targetLaw pattern) +
      -finiteEventMass sourceLaw.mass sourceLaw.states
        (threeBlockPatternEvent sourceLaw pattern)) _ ?_ hbound
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr'
      (Q'.eqv_symm
        (finiteEventMass_threeBlockPatternEvent targetLaw pattern))
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm
          (finiteEventMass_threeBlockPatternEvent sourceLaw pattern))))

theorem threeBlockPattern_source_excess_le_outgoingLeakage
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states jointMass)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass sourceLaw pattern +
        -threeBlockPatternMass targetLaw pattern ≤
      threeBlockPatternOutgoingLeakage sourceLaw targetLaw jointMass pattern := by
  have hbound := finiteEvent_source_excess_le_outgoingLeakage
    sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states
    (threeBlockPatternEvent sourceLaw pattern)
    (threeBlockPatternEvent targetLaw pattern) jointMass coupling
  unfold threeBlockPatternOutgoingLeakage
  refine Q'.le_trans' _
    (finiteEventMass sourceLaw.mass sourceLaw.states
        (threeBlockPatternEvent sourceLaw pattern) +
      -finiteEventMass targetLaw.mass targetLaw.states
        (threeBlockPatternEvent targetLaw pattern)) _ ?_ hbound
  exact Q'.le_of_eqv
    (Q'.add_eqv_congr'
      (Q'.eqv_symm
        (finiteEventMass_threeBlockPatternEvent sourceLaw pattern))
      (Q'.neg_eqv_congr _ _
        (Q'.eqv_symm
          (finiteEventMass_threeBlockPatternEvent targetLaw pattern))))

/-- A uniform two-sided leakage budget on every one of the eight block
patterns.  A physical implementation must derive `budget` from exact local
amplitudes. -/
def ThreeBlockPatternLeakageBound {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q') (budget : Q') : Prop :=
  ∀ pattern,
    threeBlockPatternIncomingLeakage sourceLaw targetLaw jointMass pattern ≤
        budget ∧
      threeBlockPatternOutgoingLeakage sourceLaw targetLaw jointMass pattern ≤
        budget

/-- A derived leakage budget directly bounds the signed discrepancy of every
physical three-block cell law in both directions. -/
theorem threeBlockPattern_cell_discrepancy_bounded
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states jointMass)
    (budget : Q')
    (hleak : ThreeBlockPatternLeakageBound
      sourceLaw targetLaw jointMass budget)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass targetLaw pattern +
          -threeBlockPatternMass sourceLaw pattern ≤ budget ∧
      threeBlockPatternMass sourceLaw pattern +
          -threeBlockPatternMass targetLaw pattern ≤ budget := by
  exact ⟨Q'.le_trans' _ _ _
      (threeBlockPattern_target_excess_le_incomingLeakage
        sourceLaw targetLaw jointMass coupling pattern)
      (hleak pattern).1,
    Q'.le_trans' _ _ _
      (threeBlockPattern_source_excess_le_outgoingLeakage
        sourceLaw targetLaw jointMass coupling pattern)
      (hleak pattern).2⟩

theorem threeBlockPattern_strict_target_excess_forces_incomingLeakage
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states jointMass)
    (pattern : ThreeBlockPattern)
    (hexcess : threeBlockPatternMass sourceLaw pattern <
      threeBlockPatternMass targetLaw pattern) :
    (0 : Q') < threeBlockPatternIncomingLeakage
      sourceLaw targetLaw jointMass pattern := by
  have hpositive : (0 : Q') <
      threeBlockPatternMass targetLaw pattern +
        -threeBlockPatternMass sourceLaw pattern :=
    YMGap.Continuum.DefectRecursionPrimary.sub_pos_of_lt hexcess
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hpositive
    (threeBlockPattern_target_excess_le_incomingLeakage
      sourceLaw targetLaw jointMass coupling pattern)

theorem threeBlockPattern_strict_source_excess_forces_outgoingLeakage
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (coupling : PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states jointMass)
    (pattern : ThreeBlockPattern)
    (hexcess : threeBlockPatternMass targetLaw pattern <
      threeBlockPatternMass sourceLaw pattern) :
    (0 : Q') < threeBlockPatternOutgoingLeakage
      sourceLaw targetLaw jointMass pattern := by
  have hpositive : (0 : Q') <
      threeBlockPatternMass sourceLaw pattern +
        -threeBlockPatternMass targetLaw pattern :=
    YMGap.Continuum.DefectRecursionPrimary.sub_pos_of_lt hexcess
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hpositive
    (threeBlockPattern_source_excess_le_outgoingLeakage
      sourceLaw targetLaw jointMass coupling pattern)

/-! ## 3. Both branches are constructively non-vacuous -/

theorem threeBlockPatternIncomingLeakage_zero_of_patternSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (hlocal : ThreeBlockPatternSupportLocalOn
      sourceLaw targetLaw jointMass)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternIncomingLeakage sourceLaw targetLaw jointMass pattern ≈
      0 := by
  unfold threeBlockPatternIncomingLeakage finiteEventIncomingLeakage
  refine Q'.eqv_trans _
    (listQSum (fun _ => (0 : Q')) sourceLaw.states) _ ?_
    (listQSum_zero sourceLaw.states)
  apply listQSum_congr_on
  intro source hsource
  by_cases hsourcePattern : threeBlockPattern sourceLaw source = pattern
  · simp [threeBlockPatternEvent, hsourcePattern]
    exact Q'.eqv_refl 0
  · simp [threeBlockPatternEvent, hsourcePattern]
    refine Q'.eqv_trans _
      (listQSum (fun _ => (0 : Q')) targetLaw.states) _ ?_
      (listQSum_zero targetLaw.states)
    apply listQSum_congr_on
    intro target htarget
    by_cases htargetPattern : threeBlockPattern targetLaw target = pattern
    · simp [htargetPattern]
      exact hlocal source hsource target htarget (by
        intro heq
        exact hsourcePattern (heq.trans htargetPattern))
    · simp [htargetPattern]
      exact Q'.eqv_refl 0

theorem threeBlockPatternOutgoingLeakage_zero_of_patternSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (jointMass : Source → Target → Q')
    (hlocal : ThreeBlockPatternSupportLocalOn
      sourceLaw targetLaw jointMass)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternOutgoingLeakage sourceLaw targetLaw jointMass pattern ≈
      0 := by
  unfold threeBlockPatternOutgoingLeakage finiteEventOutgoingLeakage
  refine Q'.eqv_trans _
    (listQSum (fun _ => (0 : Q')) sourceLaw.states) _ ?_
    (listQSum_zero sourceLaw.states)
  apply listQSum_congr_on
  intro source hsource
  by_cases hsourcePattern : threeBlockPattern sourceLaw source = pattern
  · simp [threeBlockPatternEvent, hsourcePattern]
    refine Q'.eqv_trans _
      (listQSum (fun _ => (0 : Q')) targetLaw.states) _ ?_
      (listQSum_zero targetLaw.states)
    apply listQSum_congr_on
    intro target htarget
    by_cases htargetPattern : threeBlockPattern targetLaw target = pattern
    · simp [htargetPattern]
      exact Q'.eqv_refl 0
    · simp [htargetPattern]
      exact hlocal source hsource target htarget (by
        intro heq
        exact htargetPattern (heq.symm.trans hsourcePattern))
  · simp [threeBlockPatternEvent, hsourcePattern]
    exact Q'.eqv_refl 0

private theorem fiberConditionalJoint_patternSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw) :
    ThreeBlockPatternSupportLocalOn sourceLaw targetLaw
      (threeBlockFiberConditionalJointMass sourceLaw targetLaw matchLaw) := by
  intro source hsource target htarget hmismatch
  unfold threeBlockFiberConditionalJointMass
  have hkernel := threeBlockFiberConditionalKernel_patternSupportLocal
    sourceLaw targetLaw matchLaw.target_pattern_mass_pos
    source hsource target htarget hmismatch
  refine Q'.eqv_trans _ (sourceLaw.mass source * 0) _
    (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _ hkernel) ?_
  exact Q'.mul_zero_eqv (sourceLaw.mass source)

theorem threeBlockFiberConditionalJoint_leakageBound_zero
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw) :
    ThreeBlockPatternLeakageBound sourceLaw targetLaw
      (threeBlockFiberConditionalJointMass sourceLaw targetLaw matchLaw) 0 := by
  intro pattern
  have hlocal := fiberConditionalJoint_patternSupportLocal
    sourceLaw targetLaw matchLaw
  exact ⟨Q'.le_of_eqv
      (threeBlockPatternIncomingLeakage_zero_of_patternSupportLocal
        sourceLaw targetLaw _ hlocal pattern),
    Q'.le_of_eqv
      (threeBlockPatternOutgoingLeakage_zero_of_patternSupportLocal
        sourceLaw targetLaw _ hlocal pattern)⟩

def minimalPatternSixteenth : Q' := Q'.mkPos 1 16 (by decide)
def minimalPatternThreeSixteenth : Q' := Q'.mkPos 3 16 (by decide)
def minimalPatternThreeQuarter : Q' := Q'.mkPos 3 4 (by decide)

def minimalLeftBiasedThreeBitMass : MinimalParityState → Q'
  | (false, _, _) => minimalPatternSixteenth
  | (true, _, _) => minimalPatternThreeSixteenth

def minimalLeftBiasedThreeBitLaw :
    ThreeBlockOverlapFiniteLaw MinimalParityState where
  mass := minimalLeftBiasedThreeBitMass
  states := minimalParityStateSpace
  leftParameter := minimalPatternThreeQuarter
  sharedParameter := minimalParityHalf
  rightParameter := minimalParityHalf
  leftEvent := minimalParityLeftEvent
  sharedEvent := minimalParitySharedEvent
  rightEvent := minimalParityRightEvent
  mass_nonnegative := by
    intro state
    rcases state with ⟨left, ⟨shared, right⟩⟩
    cases left <;> cases shared <;> cases right <;> decide
  left_nonnegative := by unfold minimalPatternThreeQuarter; decide
  left_le_one := by unfold minimalPatternThreeQuarter; decide
  shared_nonnegative := by unfold minimalParityHalf; decide
  shared_le_one := by unfold minimalParityHalf; decide
  right_nonnegative := by unfold minimalParityHalf; decide
  right_le_one := by unfold minimalParityHalf; decide
  left_mass := by decide
  shared_mass := by decide
  right_mass := by decide
  normalized := by decide

/-- Explicit leakage branch: transporting the uniform law to a left-biased
law changes the `000` cell from `1/8` to `1/16`, so the exact global cumulant
coupling has strictly positive outgoing leakage at that cell. -/
theorem minimalUniform_to_leftBiased_outgoingLeakage_pos :
    (0 : Q') < threeBlockPatternOutgoingLeakage
      minimalUniformThreeBitLaw minimalLeftBiasedThreeBitLaw
      (threeBlockOverlapJointMass
        minimalUniformThreeBitLaw minimalLeftBiasedThreeBitLaw)
      (false, false, false) := by
  apply threeBlockPattern_strict_source_excess_forces_outgoingLeakage
    minimalUniformThreeBitLaw minimalLeftBiasedThreeBitLaw
    (threeBlockOverlapJointMass
      minimalUniformThreeBitLaw minimalLeftBiasedThreeBitLaw)
    (threeBlockOverlapPositiveFiniteConfigurationCoupling
      minimalUniformThreeBitLaw minimalLeftBiasedThreeBitLaw)
    (false, false, false)
  decide

#print axioms listQSum_bool_partition
#print axioms finiteEvent_source_mass_decomposition
#print axioms finiteEvent_target_mass_decomposition
#print axioms finiteEvent_leakage_balance
#print axioms finiteEvent_target_excess_le_incomingLeakage
#print axioms finiteEvent_source_excess_le_outgoingLeakage
#print axioms threeBlockPattern_target_excess_le_incomingLeakage
#print axioms threeBlockPattern_source_excess_le_outgoingLeakage
#print axioms threeBlockPattern_cell_discrepancy_bounded
#print axioms threeBlockPattern_strict_target_excess_forces_incomingLeakage
#print axioms threeBlockPattern_strict_source_excess_forces_outgoingLeakage
#print axioms threeBlockPatternIncomingLeakage_zero_of_patternSupportLocal
#print axioms threeBlockPatternOutgoingLeakage_zero_of_patternSupportLocal
#print axioms threeBlockFiberConditionalJoint_leakageBound_zero
#print axioms minimalLeftBiasedThreeBitLaw
#print axioms minimalUniform_to_leftBiased_outgoingLeakage_pos

end YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision
