/-
# Exact pattern retuning from a full-support target law

If all eight target pattern masses are positive, its within-pattern
conditional distributions are defined constructively by exact rational
division.  Applying those conditionals to an arbitrary source law gives a
new target law whose complete eight-cell pattern distribution is exactly the
source distribution while retaining the original target conditional shape
inside each cell.

This is an exact finite block counterterm construction.  It does not assert
that the unretuned physical fine and coarse laws already match; instead it
isolates their remaining mismatch into eight derived pattern weights.
-/

import YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
import YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision

namespace YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternLeakageDecision

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Pushforward through the target's within-cell conditionals -/

def patternRetunedTargetMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    Target → Q' :=
  configurationPushforward sourceLaw.mass sourceLaw.states
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)

theorem patternRetunedTargetMass_nonnegative {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    (0 : Q') ≤ patternRetunedTargetMass
      sourceLaw targetLaw htargetPos target := by
  unfold patternRetunedTargetMass configurationPushforward
  apply listQSum_nonnegative_on
  intro source _
  exact Q'.mul_nonneg _ _ (sourceLaw.mass_nonnegative source)
    (threeBlockFiberConditionalKernel_nonnegative
      sourceLaw targetLaw htargetPos source target)

theorem patternRetunedTargetMass_normalized {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    listQSum (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states ≈ 1 := by
  unfold patternRetunedTargetMass configurationPushforward
  refine Q'.eqv_trans _
    (listQSum
      (fun source => listQSum
        (fun target => sourceLaw.mass source *
          threeBlockFiberConditionalKernel
            sourceLaw targetLaw htargetPos source target)
        targetLaw.states)
      sourceLaw.states) _ ?_ ?_
  · exact listQSum_swap
      (fun source target => sourceLaw.mass source *
        threeBlockFiberConditionalKernel
          sourceLaw targetLaw htargetPos source target)
      sourceLaw.states targetLaw.states
  refine Q'.eqv_trans _ (listQSum sourceLaw.mass sourceLaw.states) _ ?_
    sourceLaw.normalized
  apply listQSum_congr_on
  intro source _
  refine Q'.eqv_trans _
    (sourceLaw.mass source *
      listQSum
        (threeBlockFiberConditionalKernel
          sourceLaw targetLaw htargetPos source)
        targetLaw.states) _
    (listQSum_mul_left (sourceLaw.mass source)
      (threeBlockFiberConditionalKernel
        sourceLaw targetLaw htargetPos source)
      targetLaw.states) ?_
  refine Q'.eqv_trans _ (sourceLaw.mass source * 1) _
    (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _
      (threeBlockFiberConditionalKernel_row_normalized
        sourceLaw targetLaw htargetPos source)) ?_
  exact Q'.mul_one_eqv (sourceLaw.mass source)

/-! ## 2. Coordinate support locality and marginal preservation -/

theorem patternConditionalKernel_leftSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    CylinderSupportLocalOn sourceLaw.states targetLaw.states
      sourceLaw.leftEvent targetLaw.leftEvent
      (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos) := by
  intro source hsource target htarget hmismatch
  apply threeBlockFiberConditionalKernel_patternSupportLocal
    sourceLaw targetLaw htargetPos source hsource target htarget
  intro hpattern
  exact hmismatch (congrArg Prod.fst hpattern)

theorem patternConditionalKernel_sharedSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    CylinderSupportLocalOn sourceLaw.states targetLaw.states
      sourceLaw.sharedEvent targetLaw.sharedEvent
      (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos) := by
  intro source hsource target htarget hmismatch
  apply threeBlockFiberConditionalKernel_patternSupportLocal
    sourceLaw targetLaw htargetPos source hsource target htarget
  intro hpattern
  exact hmismatch (congrArg (fun pattern => pattern.2.1) hpattern)

theorem patternConditionalKernel_rightSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    CylinderSupportLocalOn sourceLaw.states targetLaw.states
      sourceLaw.rightEvent targetLaw.rightEvent
      (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos) := by
  intro source hsource target htarget hmismatch
  apply threeBlockFiberConditionalKernel_patternSupportLocal
    sourceLaw targetLaw htargetPos source hsource target htarget
  intro hpattern
  exact hmismatch (congrArg (fun pattern => pattern.2.2) hpattern)

theorem patternRetunedTargetMass_leftEvent {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states targetLaw.leftEvent ≈
      sourceLaw.leftParameter := by
  have htransport := supportLocal_pushforward_forces_eventMass_eqv
    sourceLaw.mass sourceLaw.states
    (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
    targetLaw.states sourceLaw.leftEvent targetLaw.leftEvent
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)
    (patternConditionalKernel_leftSupportLocal
      sourceLaw targetLaw htargetPos)
    (fun source _ => threeBlockFiberConditionalKernel_row_normalized
      sourceLaw targetLaw htargetPos source)
    (fun target _ => Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm htransport)
    sourceLaw.left_mass

theorem patternRetunedTargetMass_sharedEvent {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states targetLaw.sharedEvent ≈
      sourceLaw.sharedParameter := by
  have htransport := supportLocal_pushforward_forces_eventMass_eqv
    sourceLaw.mass sourceLaw.states
    (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
    targetLaw.states sourceLaw.sharedEvent targetLaw.sharedEvent
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)
    (patternConditionalKernel_sharedSupportLocal
      sourceLaw targetLaw htargetPos)
    (fun source _ => threeBlockFiberConditionalKernel_row_normalized
      sourceLaw targetLaw htargetPos source)
    (fun target _ => Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm htransport)
    sourceLaw.shared_mass

theorem patternRetunedTargetMass_rightEvent {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states targetLaw.rightEvent ≈
      sourceLaw.rightParameter := by
  have htransport := supportLocal_pushforward_forces_eventMass_eqv
    sourceLaw.mass sourceLaw.states
    (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
    targetLaw.states sourceLaw.rightEvent targetLaw.rightEvent
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)
    (patternConditionalKernel_rightSupportLocal
      sourceLaw targetLaw htargetPos)
    (fun source _ => threeBlockFiberConditionalKernel_row_normalized
      sourceLaw targetLaw htargetPos source)
    (fun target _ => Q'.eqv_refl _)
  exact Q'.eqv_trans _ _ _ (Q'.eqv_symm htransport)
    sourceLaw.right_mass

/-! ## 3. The retuned complete law and its exact eight-cell match -/

def patternRetunedTargetLaw {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    ThreeBlockOverlapFiniteLaw Target where
  mass := patternRetunedTargetMass sourceLaw targetLaw htargetPos
  states := targetLaw.states
  leftParameter := sourceLaw.leftParameter
  sharedParameter := sourceLaw.sharedParameter
  rightParameter := sourceLaw.rightParameter
  leftEvent := targetLaw.leftEvent
  sharedEvent := targetLaw.sharedEvent
  rightEvent := targetLaw.rightEvent
  mass_nonnegative := patternRetunedTargetMass_nonnegative
    sourceLaw targetLaw htargetPos
  left_nonnegative := sourceLaw.left_nonnegative
  left_le_one := sourceLaw.left_le_one
  shared_nonnegative := sourceLaw.shared_nonnegative
  shared_le_one := sourceLaw.shared_le_one
  right_nonnegative := sourceLaw.right_nonnegative
  right_le_one := sourceLaw.right_le_one
  left_mass := patternRetunedTargetMass_leftEvent
    sourceLaw targetLaw htargetPos
  shared_mass := patternRetunedTargetMass_sharedEvent
    sourceLaw targetLaw htargetPos
  right_mass := patternRetunedTargetMass_rightEvent
    sourceLaw targetLaw htargetPos
  normalized := patternRetunedTargetMass_normalized
    sourceLaw targetLaw htargetPos

theorem patternRetunedTargetLaw_pattern {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    threeBlockPattern
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) target =
      threeBlockPattern targetLaw target := by
  rfl

theorem patternRetunedTargetLaw_patternMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    threeBlockPatternMass sourceLaw pattern ≈
      threeBlockPatternMass
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) pattern := by
  apply threeBlockPatternSupportLocal_pushforward_forces_patternMass
    sourceLaw (patternRetunedTargetLaw sourceLaw targetLaw htargetPos)
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)
  · intro source hsource target htarget hmismatch
    apply threeBlockFiberConditionalKernel_patternSupportLocal
      sourceLaw targetLaw htargetPos source hsource target htarget
    exact hmismatch
  · intro source _
    exact threeBlockFiberConditionalKernel_row_normalized
      sourceLaw targetLaw htargetPos source
  · intro target _
    exact Q'.eqv_refl _

def patternRetunedTargetMatch {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (hsourcePos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass sourceLaw pattern) :
    ThreeBlockPatternMatch sourceLaw
      (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) where
  pattern_mass_eqv :=
    patternRetunedTargetLaw_patternMass_eqv sourceLaw targetLaw htargetPos
  target_pattern_mass_pos := fun pattern =>
    Q'.pos_of_lt_of_le (hsourcePos pattern)
      (Q'.le_of_eqv
        (patternRetunedTargetLaw_patternMass_eqv
          sourceLaw targetLaw htargetPos pattern))

/-! ## 4. The exact pattern-local positive coupling -/

def patternRetunedJointMass {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) (target : Target) : Q' :=
  sourceLaw.mass source *
    threeBlockFiberConditionalKernel
      sourceLaw targetLaw htargetPos source target

theorem patternRetunedJointMass_nonnegative {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) (target : Target) :
    (0 : Q') ≤ patternRetunedJointMass
      sourceLaw targetLaw htargetPos source target := by
  unfold patternRetunedJointMass
  exact Q'.mul_nonneg _ _ (sourceLaw.mass_nonnegative source)
    (threeBlockFiberConditionalKernel_nonnegative
      sourceLaw targetLaw htargetPos source target)

theorem patternRetunedJointMass_source_marginal {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (source : Source) :
    listQSum (patternRetunedJointMass
        sourceLaw targetLaw htargetPos source) targetLaw.states ≈
      sourceLaw.mass source := by
  unfold patternRetunedJointMass
  refine Q'.eqv_trans _
    (sourceLaw.mass source *
      listQSum
        (threeBlockFiberConditionalKernel
          sourceLaw targetLaw htargetPos source)
        targetLaw.states) _
    (listQSum_mul_left (sourceLaw.mass source)
      (threeBlockFiberConditionalKernel
        sourceLaw targetLaw htargetPos source)
      targetLaw.states) ?_
  refine Q'.eqv_trans _ (sourceLaw.mass source * 1) _
    (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _
      (threeBlockFiberConditionalKernel_row_normalized
        sourceLaw targetLaw htargetPos source)) ?_
  exact Q'.mul_one_eqv (sourceLaw.mass source)

theorem patternRetunedJointMass_target_marginal {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    listQSum
        (fun source => patternRetunedJointMass
          sourceLaw targetLaw htargetPos source target)
        sourceLaw.states ≈
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target := by
  exact Q'.eqv_refl _

theorem patternRetunedJointMass_normalized {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    listQSum
        (fun source => listQSum
          (patternRetunedJointMass sourceLaw targetLaw htargetPos source)
          targetLaw.states)
        sourceLaw.states ≈ 1 := by
  refine Q'.eqv_trans _ (listQSum sourceLaw.mass sourceLaw.states) _ ?_
    sourceLaw.normalized
  apply listQSum_congr_on
  intro source _
  exact patternRetunedJointMass_source_marginal
    sourceLaw targetLaw htargetPos source

def patternRetunedPositiveCoupling {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    PositiveFiniteConfigurationCoupling
      sourceLaw.mass sourceLaw.states
      (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
      targetLaw.states
      (patternRetunedJointMass sourceLaw targetLaw htargetPos) where
  nonnegative := patternRetunedJointMass_nonnegative
    sourceLaw targetLaw htargetPos
  source_marginal := patternRetunedJointMass_source_marginal
    sourceLaw targetLaw htargetPos
  target_marginal := patternRetunedJointMass_target_marginal
    sourceLaw targetLaw htargetPos
  normalized := patternRetunedJointMass_normalized
    sourceLaw targetLaw htargetPos

theorem patternRetunedJointMass_patternSupportLocal
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    ThreeBlockPatternSupportLocalOn sourceLaw
      (patternRetunedTargetLaw sourceLaw targetLaw htargetPos)
      (patternRetunedJointMass sourceLaw targetLaw htargetPos) := by
  intro source hsource target htarget hmismatch
  unfold patternRetunedJointMass
  have hkernel :=
    threeBlockFiberConditionalKernel_patternSupportLocal
      sourceLaw targetLaw htargetPos
      source hsource target htarget hmismatch
  refine Q'.eqv_trans _ (sourceLaw.mass source * 0) _
    (Q'.mul_eqv_congr_left (sourceLaw.mass source) _ _ hkernel) ?_
  exact Q'.mul_zero_eqv (sourceLaw.mass source)

theorem patternRetunedJoint_leakageBound_zero
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    ThreeBlockPatternLeakageBound sourceLaw
      (patternRetunedTargetLaw sourceLaw targetLaw htargetPos)
      (patternRetunedJointMass sourceLaw targetLaw htargetPos) 0 := by
  intro pattern
  have hlocal := patternRetunedJointMass_patternSupportLocal
    sourceLaw targetLaw htargetPos
  exact ⟨Q'.le_of_eqv
      (threeBlockPatternIncomingLeakage_zero_of_patternSupportLocal
        sourceLaw
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos)
        _ hlocal pattern),
    Q'.le_of_eqv
      (threeBlockPatternOutgoingLeakage_zero_of_patternSupportLocal
        sourceLaw
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos)
        _ hlocal pattern)⟩

/-! ## 5. Adapter for the exact outward coarse physical law -/

def outwardCoarseSubsupportLaw
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  normalizedPhysicalThreeSubsupportLaw coupling
    (Q'.le_of_lt hcoupling) 1 6 outwardCoarseQueries

theorem outwardCoarseSubsupportLaw_patternMass_pos
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    ∀ pattern,
      (0 : Q') < threeBlockPatternMass
        (outwardCoarseSubsupportLaw coupling hcoupling) pattern := by
  intro pattern
  obtain ⟨left, ⟨shared, right⟩⟩ := pattern
  have hall := outwardAllEightPatternMasses_pos coupling hcoupling
  cases left with
  | false =>
      cases shared with
      | false =>
          cases right with
          | false => exact hall.1
          | true => exact hall.2.2.2.1
      | true =>
          cases right with
          | false => exact hall.2.2.1
          | true => exact hall.2.2.2.2.2.2.1
  | true =>
      cases shared with
      | false =>
          cases right with
          | false => exact hall.2.1
          | true => exact hall.2.2.2.2.2.1
      | true =>
          cases right with
          | false => exact hall.2.2.2.2.1
          | true => exact hall.2.2.2.2.2.2.2

def retunedToOutwardCoarseLaw {Source : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (coupling : Q') (hcoupling : (0 : Q') < coupling) :
    ThreeBlockOverlapFiniteLaw EdgeLabelling :=
  patternRetunedTargetLaw sourceLaw
    (outwardCoarseSubsupportLaw coupling hcoupling)
    (outwardCoarseSubsupportLaw_patternMass_pos coupling hcoupling)

#print axioms patternRetunedTargetMass_nonnegative
#print axioms patternRetunedTargetMass_normalized
#print axioms patternConditionalKernel_leftSupportLocal
#print axioms patternRetunedTargetMass_leftEvent
#print axioms patternRetunedTargetLaw
#print axioms patternRetunedTargetLaw_patternMass_eqv
#print axioms patternRetunedTargetMatch
#print axioms patternRetunedPositiveCoupling
#print axioms patternRetunedJointMass_patternSupportLocal
#print axioms patternRetunedJoint_leakageBound_zero
#print axioms outwardCoarseSubsupportLaw_patternMass_pos
#print axioms retunedToOutwardCoarseLaw

end YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw
