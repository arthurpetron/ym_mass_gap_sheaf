/-
# Exact three-bit cylinder transport under pattern retuning

Every Boolean observable that factors through the three-block pattern is
transported exactly from the source law to the retuned target law.  Combining
that identity with the derived eight-cell defect bounds the discrepancy
between source and original target for all such cylinders at once.
-/

import YMGap.Continuum.Z4ThreeBlockPatternRetuneEventDefect

namespace YMGap.Continuum.Z4ThreeBlockPatternRetuneCylinderExact

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.ContinuumYMStack
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
open YMGap.Continuum.Z4ThreeBlockPatternRetuneEventDefect

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Arbitrary Boolean functions of the complete local pattern -/

def threeBlockPatternCylinderEvent {State : Type}
    (law : ThreeBlockOverlapFiniteLaw State)
    (test : ThreeBlockPattern → Bool) (state : State) : Bool :=
  test (threeBlockPattern law state)

theorem patternSupportLocal_patternCylinderEvent
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (kernel : Source → Target → Q')
    (hlocal : ThreeBlockPatternSupportLocalOn
      sourceLaw targetLaw kernel)
    (test : ThreeBlockPattern → Bool) :
    CylinderSupportLocalOn sourceLaw.states targetLaw.states
      (threeBlockPatternCylinderEvent sourceLaw test)
      (threeBlockPatternCylinderEvent targetLaw test) kernel := by
  intro source hsource target htarget hmismatch
  apply hlocal source hsource target htarget
  intro hpattern
  apply hmismatch
  unfold threeBlockPatternCylinderEvent
  rw [hpattern]

/-! ## 2. Exact source-to-retuned cylinder law -/

theorem patternRetunedCylinderEventMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (test : ThreeBlockPattern → Bool) :
    finiteEventMass sourceLaw.mass sourceLaw.states
        (threeBlockPatternCylinderEvent sourceLaw test) ≈
      finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states
        (threeBlockPatternCylinderEvent targetLaw test) := by
  exact supportLocal_pushforward_forces_eventMass_eqv
    sourceLaw.mass sourceLaw.states
    (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
    targetLaw.states
    (threeBlockPatternCylinderEvent sourceLaw test)
    (threeBlockPatternCylinderEvent targetLaw test)
    (threeBlockFiberConditionalKernel sourceLaw targetLaw htargetPos)
    (patternSupportLocal_patternCylinderEvent sourceLaw targetLaw _
      (threeBlockFiberConditionalKernel_patternSupportLocal
        sourceLaw targetLaw htargetPos) test)
    (fun source _ => threeBlockFiberConditionalKernel_row_normalized
      sourceLaw targetLaw htargetPos source)
    (fun target _ => Q'.eqv_refl _)

theorem patternRetunedLawCylinderEventMass_eqv
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (test : ThreeBlockPattern → Bool) :
    finiteEventMass sourceLaw.mass sourceLaw.states
        (threeBlockPatternCylinderEvent sourceLaw test) ≈
      finiteEventMass
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos).mass
        (patternRetunedTargetLaw sourceLaw targetLaw htargetPos).states
        (threeBlockPatternCylinderEvent
          (patternRetunedTargetLaw sourceLaw targetLaw htargetPos) test) := by
  exact patternRetunedCylinderEventMass_eqv
    sourceLaw targetLaw htargetPos test

/-! ## 3. Uniform source-versus-original-target cylinder defect -/

theorem sourceTargetPatternCylinder_abs_sub_le_derivedDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (test : ThreeBlockPattern → Bool) :
    absQ
        (finiteEventMass sourceLaw.mass sourceLaw.states
            (threeBlockPatternCylinderEvent sourceLaw test) +
          -finiteEventMass targetLaw.mass targetLaw.states
            (threeBlockPatternCylinderEvent targetLaw test)) ≤
      threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos := by
  have heq := patternRetunedCylinderEventMass_eqv
    sourceLaw targetLaw htargetPos test
  have harg :
      finiteEventMass sourceLaw.mass sourceLaw.states
          (threeBlockPatternCylinderEvent sourceLaw test) +
          -finiteEventMass targetLaw.mass targetLaw.states
            (threeBlockPatternCylinderEvent targetLaw test) ≈
        finiteEventMass
            (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
            targetLaw.states
            (threeBlockPatternCylinderEvent targetLaw test) +
          -finiteEventMass targetLaw.mass targetLaw.states
            (threeBlockPatternCylinderEvent targetLaw test) :=
    Q'.add_eqv_congr_right _ _ _ heq
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (absQ_eqv_congr harg))
    (patternRetunedEventMass_abs_sub_le_derivedDefect
      sourceLaw targetLaw htargetPos
      (threeBlockPatternCylinderEvent targetLaw test))

#print axioms patternSupportLocal_patternCylinderEvent
#print axioms patternRetunedCylinderEventMass_eqv
#print axioms patternRetunedLawCylinderEventMass_eqv
#print axioms sourceTargetPatternCylinder_abs_sub_le_derivedDefect

end YMGap.Continuum.Z4ThreeBlockPatternRetuneCylinderExact
