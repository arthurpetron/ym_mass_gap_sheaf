/-
# Exact fiber-conditional locality on the smallest three-block overlap

The complete-law cumulant kernel transports arbitrary three-block laws, but
it is a global refresh: it gives positive mass to targets with a different
three-bit block pattern.  This module isolates the exact frontier for strict
block support-locality.

* strict pattern support plus exact rows and pushforward forces equality of
  every complete three-bit pattern mass;
* when those eight masses agree and every target fiber has derived positive
  mass, exact division gives a nonnegative, row-normalized, pushforward-exact
  fiber-conditional kernel;
* the kernel is constructively source-dependent whenever two source patterns
  are present and a target state in one fiber has positive mass.

Thus pair and third-cumulant counterterms solve overlap normalization, while
strict pointwise locality has the sharper residual of matching the complete
eight-cell block law.
-/

import YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

namespace YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel

local infix:50 " ≈ " => Q'.eqv

abbrev ThreeBlockPattern := Bool × Bool × Bool

def threeBlockPattern {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State) (state : State) :
    ThreeBlockPattern :=
  (law.leftEvent state, law.sharedEvent state, law.rightEvent state)

def threeBlockPatternMass {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State)
    (pattern : ThreeBlockPattern) : Q' :=
  listQSum
    (fun state =>
      if threeBlockPattern law state = pattern then law.mass state else 0)
    law.states

def threeBlockPatternEvent {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State)
    (pattern : ThreeBlockPattern) (state : State) : Bool :=
  decide (threeBlockPattern law state = pattern)

theorem finiteEventMass_threeBlockPatternEvent {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State)
    (pattern : ThreeBlockPattern) :
    finiteEventMass law.mass law.states
        (threeBlockPatternEvent law pattern) ≈
      threeBlockPatternMass law pattern := by
  unfold finiteEventMass threeBlockPatternMass
  apply listQSum_congr_on
  intro state _
  by_cases hpattern : threeBlockPattern law state = pattern
  · simp [threeBlockPatternEvent, hpattern]
    exact Q'.eqv_refl _
  · simp [threeBlockPatternEvent, hpattern]
    exact Q'.eqv_refl 0

theorem threeBlockPatternMass_nonnegative {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State)
    (pattern : ThreeBlockPattern) :
    (0 : Q') ≤ threeBlockPatternMass law pattern := by
  unfold threeBlockPatternMass
  apply listQSum_nonnegative_on
  intro state _
  by_cases hpattern : threeBlockPattern law state = pattern
  · simp [hpattern]
    exact law.mass_nonnegative state
  · simp [hpattern]
    exact Q'.le_refl' 0

/-! ## 1. Necessity of complete fiber-mass matching -/

/-- Selected target row mass for a support-local Boolean kernel. -/
theorem supportLocal_selected_row {Source Target : Type}
    (sourceStates : List Source) (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (kernel : Source → Target → Q')
    (hlocal : CylinderSupportLocalOn sourceStates targetStates
      sourceEvent targetEvent kernel)
    (hrow : ∀ source, source ∈ sourceStates →
      listQSum (kernel source) targetStates ≈ 1)
    (source : Source) (hsource : source ∈ sourceStates) :
    listQSum
        (fun target => if targetEvent target then kernel source target else 0)
        targetStates ≈
      if sourceEvent source then 1 else 0 := by
  cases hsourceEvent : sourceEvent source
  · change listQSum
      (fun target => if targetEvent target then kernel source target else 0)
        targetStates ≈ 0
    refine Q'.eqv_trans _
      (listQSum (fun _ => (0 : Q')) targetStates) _ ?_
      (listQSum_zero targetStates)
    apply listQSum_congr_on
    intro target htarget
    cases htargetEvent : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_refl 0
    · simp only [if_true]
      exact hlocal source hsource target htarget (by
        rw [hsourceEvent, htargetEvent]
        decide)
  · change listQSum
      (fun target => if targetEvent target then kernel source target else 0)
        targetStates ≈ 1
    refine Q'.eqv_trans _ (listQSum (kernel source) targetStates) _ ?_
      (hrow source hsource)
    apply listQSum_congr_on
    intro target htarget
    cases htargetEvent : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      exact Q'.eqv_symm
        (hlocal source hsource target htarget (by
          rw [hsourceEvent, htargetEvent]
          decide))
    · simp only [if_true]
      exact Q'.eqv_refl _

/-- Even the weakest event-support locality forces equality of the selected
event masses under exact row normalization and exact pushforward. -/
theorem supportLocal_pushforward_forces_eventMass_eqv
    {Source Target : Type}
    (sourceMass : Source → Q') (sourceStates : List Source)
    (targetMass : Target → Q') (targetStates : List Target)
    (sourceEvent : Source → Bool) (targetEvent : Target → Bool)
    (kernel : Source → Target → Q')
    (hlocal : CylinderSupportLocalOn sourceStates targetStates
      sourceEvent targetEvent kernel)
    (hrow : ∀ source, source ∈ sourceStates →
      listQSum (kernel source) targetStates ≈ 1)
    (hpush : ∀ target, target ∈ targetStates →
      configurationPushforward sourceMass sourceStates kernel target ≈
        targetMass target) :
    finiteEventMass sourceMass sourceStates sourceEvent ≈
      finiteEventMass targetMass targetStates targetEvent := by
  let selectedJoint := fun target source =>
    if targetEvent target then sourceMass source * kernel source target else 0
  have htarget :
      finiteEventMass targetMass targetStates targetEvent ≈
        listQSum
          (fun target => listQSum (selectedJoint target) sourceStates)
          targetStates := by
    unfold finiteEventMass
    apply listQSum_congr_on
    intro target htargetMem
    cases hevent : targetEvent target
    · simp only [Bool.false_eq_true, if_false]
      unfold selectedJoint
      simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (listQSum_zero sourceStates)
    · simp only [if_true]
      unfold selectedJoint
      simp only [hevent, if_true]
      exact Q'.eqv_symm (hpush target htargetMem)
  have hsource :
      listQSum
          (fun source => listQSum
            (fun target => selectedJoint target source) targetStates)
          sourceStates ≈
        finiteEventMass sourceMass sourceStates sourceEvent := by
    unfold finiteEventMass
    apply listQSum_congr_on
    intro source hsourceMem
    refine Q'.eqv_trans _
      (sourceMass source *
        listQSum
          (fun target => if targetEvent target then kernel source target else 0)
          targetStates) _ ?_ ?_
    · refine Q'.eqv_trans _
        (listQSum
          (fun target => sourceMass source *
            (if targetEvent target then kernel source target else 0))
          targetStates) _ ?_ ?_
      · apply listQSum_congr_on
        intro target _
        cases hevent : targetEvent target
        · simp [selectedJoint, hevent]
          exact Q'.eqv_symm (Q'.mul_zero_eqv (sourceMass source))
        · simp [selectedJoint, hevent]
          exact Q'.eqv_refl _
      exact listQSum_mul_left (sourceMass source)
        (fun target => if targetEvent target then kernel source target else 0)
        targetStates
    have hselected := supportLocal_selected_row
      sourceStates targetStates sourceEvent targetEvent kernel
      hlocal hrow source hsourceMem
    cases hevent : sourceEvent source
    · simp only [Bool.false_eq_true, if_false]
      rw [hevent] at hselected
      simp only [Bool.false_eq_true, if_false] at hselected
      refine Q'.eqv_trans _ (sourceMass source * 0) _
        (Q'.mul_eqv_congr_left (sourceMass source) _ _ hselected) ?_
      exact Q'.mul_zero_eqv (sourceMass source)
    · simp only [if_true]
      rw [hevent] at hselected
      simp only [if_true] at hselected
      refine Q'.eqv_trans _ (sourceMass source * 1) _
        (Q'.mul_eqv_congr_left (sourceMass source) _ _ hselected) ?_
      exact Q'.mul_one_eqv (sourceMass source)
  refine Q'.eqv_symm (Q'.eqv_trans _ _ _ htarget ?_)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_swap selectedJoint targetStates sourceStates))
    hsource

/-- Strict equality of the whole three-bit support pattern. -/
def ThreeBlockPatternSupportLocalOn {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (kernel : Source → Target → Q') : Prop :=
  ∀ source, source ∈ sourceLaw.states →
    ∀ target, target ∈ targetLaw.states →
      threeBlockPattern sourceLaw source ≠
          threeBlockPattern targetLaw target →
        kernel source target ≈ 0

theorem threeBlockPatternSupportLocal_patternEvent
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (kernel : Source → Target → Q')
    (hlocal : ThreeBlockPatternSupportLocalOn sourceLaw targetLaw kernel)
    (pattern : ThreeBlockPattern) :
    CylinderSupportLocalOn sourceLaw.states targetLaw.states
      (threeBlockPatternEvent sourceLaw pattern)
      (threeBlockPatternEvent targetLaw pattern) kernel := by
  intro source hsource target htarget hmismatch
  apply hlocal source hsource target htarget
  intro hpatterns
  apply hmismatch
  unfold threeBlockPatternEvent
  rw [hpatterns]

/-- Machine-checked locality obstruction: every one of the eight cell masses
must agree before a strict three-block support-local exact transport can
exist. -/
theorem threeBlockPatternSupportLocal_pushforward_forces_patternMass
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (kernel : Source → Target → Q')
    (hlocal : ThreeBlockPatternSupportLocalOn sourceLaw targetLaw kernel)
    (hrow : ∀ source, source ∈ sourceLaw.states →
      listQSum (kernel source) targetLaw.states ≈ 1)
    (hpush : ∀ target, target ∈ targetLaw.states →
      configurationPushforward sourceLaw.mass sourceLaw.states kernel target ≈
        targetLaw.mass target)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass sourceLaw pattern ≈
      threeBlockPatternMass targetLaw pattern := by
  refine Q'.eqv_trans _
    (finiteEventMass sourceLaw.mass sourceLaw.states
      (threeBlockPatternEvent sourceLaw pattern)) _
    (Q'.eqv_symm
      (finiteEventMass_threeBlockPatternEvent sourceLaw pattern)) ?_
  refine Q'.eqv_trans _
    (finiteEventMass targetLaw.mass targetLaw.states
      (threeBlockPatternEvent targetLaw pattern)) _ ?_
    (finiteEventMass_threeBlockPatternEvent targetLaw pattern)
  exact supportLocal_pushforward_forces_eventMass_eqv
    sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states
    (threeBlockPatternEvent sourceLaw pattern)
    (threeBlockPatternEvent targetLaw pattern) kernel
    (threeBlockPatternSupportLocal_patternEvent
      sourceLaw targetLaw kernel hlocal pattern)
    hrow hpush

/-! ## 2. Exact construction when the necessary cell laws match -/

structure ThreeBlockPatternMatch {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target) : Prop where
  pattern_mass_eqv : ∀ pattern,
    threeBlockPatternMass sourceLaw pattern ≈
      threeBlockPatternMass targetLaw pattern
  target_pattern_mass_pos : ∀ pattern,
    (0 : Q') < threeBlockPatternMass targetLaw pattern

def targetThreeBlockFiberConditionalMass {Target : Type}
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) : Q' :=
  Q'.divPos (targetLaw.mass target)
    (threeBlockPatternMass targetLaw (threeBlockPattern targetLaw target))
    (hpositive (threeBlockPattern targetLaw target))

def threeBlockFiberConditionalKernel {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) (target : Target) : Q' :=
  if threeBlockPattern targetLaw target = threeBlockPattern sourceLaw source then
    targetThreeBlockFiberConditionalMass targetLaw hpositive target
  else 0

theorem targetThreeBlockFiberConditionalMass_nonnegative {Target : Type}
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    (0 : Q') ≤ targetThreeBlockFiberConditionalMass
      targetLaw hpositive target := by
  unfold targetThreeBlockFiberConditionalMass Q'.divPos
  exact Q'.mul_nonneg _ _ (targetLaw.mass_nonnegative target)
    (Q'.le_of_lt (Q'.recipPos_pos _ _))

theorem threeBlockFiberConditionalKernel_nonnegative {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) (target : Target) :
    (0 : Q') ≤ threeBlockFiberConditionalKernel
      sourceLaw targetLaw hpositive source target := by
  unfold threeBlockFiberConditionalKernel
  by_cases hpattern :
      threeBlockPattern targetLaw target = threeBlockPattern sourceLaw source
  · rw [if_pos hpattern]
    exact targetThreeBlockFiberConditionalMass_nonnegative
      targetLaw hpositive target
  · rw [if_neg hpattern]
    exact Q'.le_refl' 0

theorem threeBlockFiberConditionalKernel_patternSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    ThreeBlockPatternSupportLocalOn sourceLaw targetLaw
      (threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive) := by
  intro source _ target _ hmismatch
  unfold threeBlockFiberConditionalKernel
  rw [if_neg]
  exact Q'.eqv_refl 0
  exact fun heq => hmismatch heq.symm

/-- The row depends only on the source's bounded three-block pattern. -/
theorem threeBlockFiberConditionalKernel_source_pattern_local
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source source' : Source)
    (hpattern : threeBlockPattern sourceLaw source =
      threeBlockPattern sourceLaw source')
    (target : Target) :
    threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
        source target ≈
      threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
        source' target := by
  unfold threeBlockFiberConditionalKernel
  rw [hpattern]
  exact Q'.eqv_refl _

private theorem targetFiberConditional_eqv_fixed_pattern {Target : Type}
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) (pattern : ThreeBlockPattern)
    (hpattern : threeBlockPattern targetLaw target = pattern) :
    targetThreeBlockFiberConditionalMass targetLaw hpositive target ≈
      Q'.divPos (targetLaw.mass target)
        (threeBlockPatternMass targetLaw pattern) (hpositive pattern) := by
  subst pattern
  exact Q'.eqv_refl _

theorem threeBlockFiberConditionalKernel_row_normalized
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) :
    listQSum
        (threeBlockFiberConditionalKernel
          sourceLaw targetLaw hpositive source) targetLaw.states ≈ 1 := by
  let pattern := threeBlockPattern sourceLaw source
  let denominator := threeBlockPatternMass targetLaw pattern
  let reciprocal := Q'.recipPos denominator (hpositive pattern)
  let filtered := fun target =>
    if threeBlockPattern targetLaw target = pattern then
      targetLaw.mass target else 0
  refine Q'.eqv_trans _
    (listQSum (fun target => reciprocal * filtered target)
      targetLaw.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro target _
    by_cases hpattern : threeBlockPattern targetLaw target = pattern
    · rw [threeBlockFiberConditionalKernel, if_pos]
      · unfold filtered
        rw [if_pos hpattern]
        refine Q'.eqv_trans _
          (Q'.divPos (targetLaw.mass target) denominator
            (hpositive pattern)) _ ?_ ?_
        · exact targetFiberConditional_eqv_fixed_pattern
            targetLaw hpositive target pattern hpattern
        unfold Q'.divPos reciprocal
        exact Q'.mul_comm_eqv (targetLaw.mass target)
          (Q'.recipPos denominator (hpositive pattern))
      · exact hpattern
    · rw [threeBlockFiberConditionalKernel, if_neg]
      · unfold filtered
        rw [if_neg hpattern]
        exact Q'.eqv_symm (Q'.mul_zero_eqv reciprocal)
      · exact hpattern
  refine Q'.eqv_trans _
    (reciprocal * listQSum filtered targetLaw.states) _
    (listQSum_mul_left reciprocal filtered targetLaw.states) ?_
  change reciprocal * denominator ≈ 1
  refine Q'.eqv_trans _ (denominator * reciprocal) _
    (Q'.mul_comm_eqv reciprocal denominator) ?_
  exact Q'.mul_recipPos_eqv denominator (hpositive pattern)

theorem threeBlockFiberConditionalKernel_pushforward
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw)
    (target : Target) :
    configurationPushforward sourceLaw.mass sourceLaw.states
        (threeBlockFiberConditionalKernel sourceLaw targetLaw
          matchLaw.target_pattern_mass_pos) target ≈
      targetLaw.mass target := by
  let pattern := threeBlockPattern targetLaw target
  let conditional := targetThreeBlockFiberConditionalMass targetLaw
    matchLaw.target_pattern_mass_pos target
  let filtered := fun source =>
    if threeBlockPattern sourceLaw source = pattern then
      sourceLaw.mass source else 0
  unfold configurationPushforward
  refine Q'.eqv_trans _
    (listQSum (fun source => conditional * filtered source)
      sourceLaw.states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source _
    by_cases hpattern :
        threeBlockPattern targetLaw target = threeBlockPattern sourceLaw source
    · rw [threeBlockFiberConditionalKernel, if_pos hpattern]
      unfold filtered
      have hsourcePattern : threeBlockPattern sourceLaw source = pattern := by
        exact hpattern.symm
      rw [if_pos hsourcePattern]
      exact Q'.mul_comm_eqv (sourceLaw.mass source) conditional
    · rw [threeBlockFiberConditionalKernel, if_neg hpattern]
      unfold filtered
      have hsourcePattern : threeBlockPattern sourceLaw source ≠ pattern := by
        intro heq
        apply hpattern
        exact heq.symm
      rw [if_neg hsourcePattern]
      exact Q'.eqv_trans _ (0 : Q') _
        (Q'.mul_zero_eqv (sourceLaw.mass source))
        (Q'.eqv_symm (Q'.mul_zero_eqv conditional))
  refine Q'.eqv_trans _
    (conditional * listQSum filtered sourceLaw.states) _
    (listQSum_mul_left conditional filtered sourceLaw.states) ?_
  change conditional * threeBlockPatternMass sourceLaw pattern ≈
    targetLaw.mass target
  refine Q'.eqv_trans _
    (conditional * threeBlockPatternMass targetLaw pattern) _
    (Q'.mul_eqv_congr_left conditional _ _
      (matchLaw.pattern_mass_eqv pattern)) ?_
  unfold conditional targetThreeBlockFiberConditionalMass pattern
  exact Q'.divPos_mul_eqv _ _ _

def threeBlockFiberConditionalJointMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw)
    (source : Source) (target : Target) : Q' :=
  sourceLaw.mass source *
    threeBlockFiberConditionalKernel sourceLaw targetLaw
      matchLaw.target_pattern_mass_pos source target

theorem threeBlockFiberConditionalJointMass_nonnegative
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw)
    (source : Source) (target : Target) :
    (0 : Q') ≤ threeBlockFiberConditionalJointMass
      sourceLaw targetLaw matchLaw source target := by
  unfold threeBlockFiberConditionalJointMass
  exact Q'.mul_nonneg _ _ (sourceLaw.mass_nonnegative source)
    (threeBlockFiberConditionalKernel_nonnegative sourceLaw targetLaw
      matchLaw.target_pattern_mass_pos source target)

theorem threeBlockFiberConditionalJointMass_source_marginal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw)
    (source : Source) :
    listQSum
        (threeBlockFiberConditionalJointMass
          sourceLaw targetLaw matchLaw source) targetLaw.states ≈
      sourceLaw.mass source := by
  unfold threeBlockFiberConditionalJointMass
  refine Q'.eqv_trans _
    (sourceLaw.mass source *
      listQSum
        (threeBlockFiberConditionalKernel sourceLaw targetLaw
          matchLaw.target_pattern_mass_pos source) targetLaw.states) _
    (listQSum_mul_left (sourceLaw.mass source) _ targetLaw.states) ?_
  refine Q'.eqv_trans _ (sourceLaw.mass source * 1) _
    (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _
      (threeBlockFiberConditionalKernel_row_normalized
        sourceLaw targetLaw matchLaw.target_pattern_mass_pos source)) ?_
  exact Q'.mul_one_eqv (sourceLaw.mass source)

theorem threeBlockFiberConditionalJointMass_target_marginal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw)
    (target : Target) :
    listQSum
        (fun source => threeBlockFiberConditionalJointMass
          sourceLaw targetLaw matchLaw source target) sourceLaw.states ≈
      targetLaw.mass target := by
  change configurationPushforward sourceLaw.mass sourceLaw.states
      (threeBlockFiberConditionalKernel sourceLaw targetLaw
        matchLaw.target_pattern_mass_pos) target ≈ targetLaw.mass target
  exact threeBlockFiberConditionalKernel_pushforward
    sourceLaw targetLaw matchLaw target

theorem threeBlockFiberConditionalJointMass_normalized
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw) :
    listQSum
        (fun source => listQSum
          (threeBlockFiberConditionalJointMass
            sourceLaw targetLaw matchLaw source) targetLaw.states)
        sourceLaw.states ≈ 1 := by
  refine Q'.eqv_trans _ (listQSum sourceLaw.mass sourceLaw.states) _ ?_
    sourceLaw.normalized
  apply listQSum_congr_on
  intro source _
  exact threeBlockFiberConditionalJointMass_source_marginal
    sourceLaw targetLaw matchLaw source

def threeBlockFiberConditionalPositiveCoupling
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (matchLaw : ThreeBlockPatternMatch sourceLaw targetLaw) :
    PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states targetLaw.mass targetLaw.states
      (threeBlockFiberConditionalJointMass sourceLaw targetLaw matchLaw) where
  nonnegative := threeBlockFiberConditionalJointMass_nonnegative
    sourceLaw targetLaw matchLaw
  source_marginal := threeBlockFiberConditionalJointMass_source_marginal
    sourceLaw targetLaw matchLaw
  target_marginal := threeBlockFiberConditionalJointMass_target_marginal
    sourceLaw targetLaw matchLaw
  normalized := threeBlockFiberConditionalJointMass_normalized
    sourceLaw targetLaw matchLaw

/-! ## 3. Constructive source dependence -/

theorem threeBlockFiberConditionalKernel_source_dependent
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (hpositive : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (sourceSame sourceOther : Source) (target : Target)
    (hsame : threeBlockPattern targetLaw target =
      threeBlockPattern sourceLaw sourceSame)
    (hother : threeBlockPattern targetLaw target ≠
      threeBlockPattern sourceLaw sourceOther)
    (htargetMass : (0 : Q') < targetLaw.mass target) :
    ¬ threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
        sourceSame target ≈
      threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
        sourceOther target := by
  have hsamePos : (0 : Q') <
      threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
        sourceSame target := by
    unfold threeBlockFiberConditionalKernel
    rw [if_pos hsame]
    unfold targetThreeBlockFiberConditionalMass
    exact Q'.divPos_pos _ _ _ htargetMass
  have hotherZero :
      threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
          sourceOther target ≈ 0 := by
    unfold threeBlockFiberConditionalKernel
    rw [if_neg hother]
    exact Q'.eqv_refl 0
  intro hequal
  have hzero := Q'.eqv_trans _ _ _ hequal hotherZero
  have hleZero :
      threeBlockFiberConditionalKernel sourceLaw targetLaw hpositive
          sourceSame target ≤ 0 := Q'.le_of_eqv hzero
  exact YMGap.Continuum.ClusteringImpliesGap.lt_irrefl' 0
    (YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le
      hsamePos hleZero)

/-! ## 4. Explicit non-vacuity of the matched-fiber hypotheses -/

def minimalUniformThreeBitMass : MinimalParityState → Q' :=
  fun _ => minimalParityEighth

def minimalUniformThreeBitLaw :
    ThreeBlockOverlapFiniteLaw MinimalParityState where
  mass := minimalUniformThreeBitMass
  states := minimalParityStateSpace
  leftParameter := minimalParityHalf
  sharedParameter := minimalParityHalf
  rightParameter := minimalParityHalf
  leftEvent := minimalParityLeftEvent
  sharedEvent := minimalParitySharedEvent
  rightEvent := minimalParityRightEvent
  mass_nonnegative := by
    intro state
    unfold minimalUniformThreeBitMass minimalParityEighth
    decide
  left_nonnegative := by unfold minimalParityHalf; decide
  left_le_one := by unfold minimalParityHalf; decide
  shared_nonnegative := by unfold minimalParityHalf; decide
  shared_le_one := by unfold minimalParityHalf; decide
  right_nonnegative := by unfold minimalParityHalf; decide
  right_le_one := by unfold minimalParityHalf; decide
  left_mass := by decide
  shared_mass := by decide
  right_mass := by decide
  normalized := by decide

theorem minimalUniformThreeBit_patternMass_eqv_eighth
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass minimalUniformThreeBitLaw pattern ≈
      minimalParityEighth := by
  rcases pattern with ⟨left, ⟨shared, right⟩⟩
  cases left <;> cases shared <;> cases right <;> decide

theorem minimalUniformThreeBit_patternMass_pos
    (pattern : ThreeBlockPattern) :
    (0 : Q') < threeBlockPatternMass minimalUniformThreeBitLaw pattern := by
  have heq := minimalUniformThreeBit_patternMass_eqv_eighth pattern
  exact Q'.pos_of_lt_of_le (by
      unfold minimalParityEighth
      decide) (Q'.le_of_eqv (Q'.eqv_symm heq))

def minimalUniformThreeBitSelfMatch :
    ThreeBlockPatternMatch minimalUniformThreeBitLaw
      minimalUniformThreeBitLaw where
  pattern_mass_eqv := fun _ => Q'.eqv_refl _
  target_pattern_mass_pos := minimalUniformThreeBit_patternMass_pos

/-- Concrete carrier witness: the local kernel has distinct rows on two
different three-block patterns, so neither the locality nor source dependence
certificate is vacuous. -/
theorem minimalUniformThreeBitFiberKernel_source_dependent :
    ¬ threeBlockFiberConditionalKernel
        minimalUniformThreeBitLaw minimalUniformThreeBitLaw
        minimalUniformThreeBit_patternMass_pos
        (false, false, false) (false, false, false) ≈
      threeBlockFiberConditionalKernel
        minimalUniformThreeBitLaw minimalUniformThreeBitLaw
        minimalUniformThreeBit_patternMass_pos
        (true, false, false) (false, false, false) := by
  apply threeBlockFiberConditionalKernel_source_dependent
    minimalUniformThreeBitLaw minimalUniformThreeBitLaw
    minimalUniformThreeBit_patternMass_pos
    (false, false, false) (true, false, false) (false, false, false)
  · rfl
  · decide
  · unfold minimalUniformThreeBitLaw minimalUniformThreeBitMass
      minimalParityEighth
    decide

#print axioms supportLocal_pushforward_forces_eventMass_eqv
#print axioms threeBlockPatternSupportLocal_pushforward_forces_patternMass
#print axioms threeBlockFiberConditionalKernel_nonnegative
#print axioms threeBlockFiberConditionalKernel_patternSupportLocal
#print axioms threeBlockFiberConditionalKernel_source_pattern_local
#print axioms threeBlockFiberConditionalKernel_row_normalized
#print axioms threeBlockFiberConditionalKernel_pushforward
#print axioms threeBlockFiberConditionalPositiveCoupling
#print axioms threeBlockFiberConditionalKernel_source_dependent
#print axioms minimalUniformThreeBit_patternMass_pos
#print axioms minimalUniformThreeBitSelfMatch
#print axioms minimalUniformThreeBitFiberKernel_source_dependent

end YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
