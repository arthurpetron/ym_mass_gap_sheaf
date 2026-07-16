/-
# Event-level transport of the three-block retune defect

The exact pattern defect bounds every target atom.  Finite summation therefore
transports the same multiplicative envelope to every Boolean event on the
target state space.  This is the cylinder-probability form needed by later
correlation and scale-recursion arguments.
-/

import YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope

namespace YMGap.Continuum.Z4ThreeBlockPatternRetuneEventDefect

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw
open YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Constructive termwise order for exact finite sums -/

theorem listQSum_le_termwise {A : Type} (left right : A → Q') :
    ∀ xs : List A,
      (∀ x, x ∈ xs → left x ≤ right x) →
      listQSum left xs ≤ listQSum right xs
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise left right tail
          (fun x hx => hle x (List.mem_cons_of_mem head hx)))

/-! ## 2. An arbitrary relative envelope survives event summation -/

theorem patternRetunedEventMass_lower_bound_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (event : Target → Bool) :
    lower * finiteEventMass targetLaw.mass targetLaw.states event ≤
      finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states event := by
  unfold finiteEventMass
  let targetSelected := fun target =>
    if event target then targetLaw.mass target else 0
  let lowerSelected := fun target =>
    if event target then lower * targetLaw.mass target else 0
  let retunedSelected := fun target =>
    if event target then
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target else 0
  have hfactor :
      lower * listQSum targetSelected targetLaw.states ≈
        listQSum lowerSelected targetLaw.states := by
    refine Q'.eqv_trans _
      (listQSum (fun target => lower * targetSelected target)
        targetLaw.states) _
      (Q'.eqv_symm
        (listQSum_mul_left lower targetSelected targetLaw.states)) ?_
    apply listQSum_congr_on
    intro target _
    cases hevent : event target
    · unfold targetSelected lowerSelected
      simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.mul_zero_eqv lower
    · unfold targetSelected lowerSelected
      simp only [hevent, if_true]
      exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor) ?_
  apply listQSum_le_termwise lowerSelected retunedSelected
  intro target _
  cases hevent : event target
  · unfold lowerSelected retunedSelected
    simp only [hevent, Bool.false_eq_true, if_false]
    exact Q'.le_refl' 0
  · unfold lowerSelected retunedSelected
    simp only [hevent, if_true]
    exact patternRetunedTargetMass_lower_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope target

theorem patternRetunedEventMass_upper_bound_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (event : Target → Bool) :
    finiteEventMass
        (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
        targetLaw.states event ≤
      upper * finiteEventMass targetLaw.mass targetLaw.states event := by
  unfold finiteEventMass
  let targetSelected := fun target =>
    if event target then targetLaw.mass target else 0
  let upperSelected := fun target =>
    if event target then upper * targetLaw.mass target else 0
  let retunedSelected := fun target =>
    if event target then
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target else 0
  have hfactor :
      listQSum upperSelected targetLaw.states ≈
        upper * listQSum targetSelected targetLaw.states := by
    refine Q'.eqv_trans _
      (listQSum (fun target => upper * targetSelected target)
        targetLaw.states) _ ?_
      (listQSum_mul_left upper targetSelected targetLaw.states)
    apply listQSum_congr_on
    intro target _
    cases hevent : event target
    · unfold targetSelected upperSelected
      simp only [hevent, Bool.false_eq_true, if_false]
      exact Q'.eqv_symm (Q'.mul_zero_eqv upper)
    · unfold targetSelected upperSelected
      simp only [hevent, if_true]
      exact Q'.eqv_refl _
  refine Q'.le_trans' _ _ _ ?_ (Q'.le_of_eqv hfactor)
  apply listQSum_le_termwise retunedSelected upperSelected
  intro target _
  cases hevent : event target
  · unfold retunedSelected upperSelected
    simp only [hevent, Bool.false_eq_true, if_false]
    exact Q'.le_refl' 0
  · unfold retunedSelected upperSelected
    simp only [hevent, if_true]
    exact patternRetunedTargetMass_upper_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope target

theorem patternRetunedEventMass_bounds_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (event : Target → Bool) :
    lower * finiteEventMass targetLaw.mass targetLaw.states event ≤
        finiteEventMass
          (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
          targetLaw.states event ∧
      finiteEventMass
          (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
          targetLaw.states event ≤
        upper * finiteEventMass targetLaw.mass targetLaw.states event := by
  exact ⟨patternRetunedEventMass_lower_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope event,
    patternRetunedEventMass_upper_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope event⟩

/-! ## 3. Every event is controlled by the exact derived eight-cell defect -/

theorem patternRetunedEventMass_bounds_by_derivedDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (event : Target → Bool) :
    ((1 : Q') + -threeBlockPatternRetuneDefect
        sourceLaw targetLaw htargetPos) *
        finiteEventMass targetLaw.mass targetLaw.states event ≤
        finiteEventMass
          (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
          targetLaw.states event ∧
      finiteEventMass
          (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
          targetLaw.states event ≤
        ((1 : Q') + threeBlockPatternRetuneDefect
          sourceLaw targetLaw htargetPos) *
          finiteEventMass targetLaw.mass targetLaw.states event := by
  exact patternRetunedEventMass_bounds_of_relativeEnvelope
    sourceLaw targetLaw htargetPos
    (derivedDefectRelativeEnvelope sourceLaw targetLaw htargetPos) event

/-! ## 4. Absolute event error and a finite total-variation envelope -/

theorem one_add_mul_add_neg_self_eqv (defect probability : Q') :
    (((1 : Q') + defect) * probability) + -probability ≈
      defect * probability := by
  refine Q'.eqv_trans _
    (((1 : Q') * probability + defect * probability) + -probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_mul_eqv (1 : Q') defect probability)) ?_
  refine Q'.eqv_trans _
    ((probability + defect * probability) + -probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.one_mul_eqv probability))) ?_
  refine Q'.eqv_trans _
    (probability + (defect * probability + -probability)) _
    (Q'.add_assoc_eqv probability (defect * probability) (-probability)) ?_
  refine Q'.eqv_trans _
    (probability + (-probability + defect * probability)) _
    (Q'.add_eqv_congr_left probability _ _
      (Q'.add_comm_eqv (defect * probability) (-probability))) ?_
  refine Q'.eqv_trans _
    ((probability + -probability) + defect * probability) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv probability (-probability)
        (defect * probability))) ?_
  refine Q'.eqv_trans _ (0 + defect * probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv probability)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (defect * probability))

theorem one_add_neg_mul_add_neg_self_eqv (defect probability : Q') :
    (((1 : Q') + -defect) * probability) + -probability ≈
      -(defect * probability) := by
  refine Q'.eqv_trans _
    (((1 : Q') * probability + (-defect) * probability) + -probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_mul_eqv (1 : Q') (-defect) probability)) ?_
  refine Q'.eqv_trans _
    ((probability + (-defect) * probability) + -probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.one_mul_eqv probability))) ?_
  refine Q'.eqv_trans _
    ((probability + -(defect * probability)) + -probability) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_left probability _ _
        (Q'.neg_mul_eqv defect probability))) ?_
  refine Q'.eqv_trans _
    (probability + (-(defect * probability) + -probability)) _
    (Q'.add_assoc_eqv probability (-(defect * probability))
      (-probability)) ?_
  refine Q'.eqv_trans _
    (probability + (-probability + -(defect * probability))) _
    (Q'.add_eqv_congr_left probability _ _
      (Q'.add_comm_eqv (-(defect * probability)) (-probability))) ?_
  refine Q'.eqv_trans _
    ((probability + -probability) + -(defect * probability)) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv probability (-probability)
        (-(defect * probability)))) ?_
  refine Q'.eqv_trans _ (0 + -(defect * probability)) _
    (Q'.add_eqv_congr_right _ _ _
      (Q'.add_neg_self_eqv probability)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' (-(defect * probability)))

theorem patternRetunedEventMass_abs_sub_le_scaledDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (event : Target → Bool) :
    absQ
        (finiteEventMass
            (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
            targetLaw.states event +
          -finiteEventMass targetLaw.mass targetLaw.states event) ≤
      threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos *
        finiteEventMass targetLaw.mass targetLaw.states event := by
  let defect := threeBlockPatternRetuneDefect
    sourceLaw targetLaw htargetPos
  let targetEventMass :=
    finiteEventMass targetLaw.mass targetLaw.states event
  let retunedEventMass := finiteEventMass
    (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
    targetLaw.states event
  have hbounds := patternRetunedEventMass_bounds_by_derivedDefect
    sourceLaw targetLaw htargetPos event
  have hlower : -(defect * targetEventMass) ≤
      retunedEventMass + -targetEventMass := by
    have hstep := Q'.add_le_add_right _ _ (-targetEventMass) hbounds.1
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (one_add_neg_mul_add_neg_self_eqv defect targetEventMass)) hstep
  have hupper : retunedEventMass + -targetEventMass ≤
      defect * targetEventMass := by
    have hstep := Q'.add_le_add_right _ _ (-targetEventMass) hbounds.2
    exact Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv
        (one_add_mul_add_neg_self_eqv defect targetEventMass))
  exact absQ_le hlower hupper

theorem patternRetunedEventMass_abs_sub_le_derivedDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (event : Target → Bool) :
    absQ
        (finiteEventMass
            (patternRetunedTargetMass sourceLaw targetLaw htargetPos)
            targetLaw.states event +
          -finiteEventMass targetLaw.mass targetLaw.states event) ≤
      threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos := by
  have hscaled := patternRetunedEventMass_abs_sub_le_scaledDefect
    sourceLaw targetLaw htargetPos event
  have heventLe : finiteEventMass targetLaw.mass targetLaw.states event ≤
      (1 : Q') :=
    finiteEventMass_le_one targetLaw.mass targetLaw.states event
      (fun target _ => targetLaw.mass_nonnegative target)
      targetLaw.normalized
  have hdefectNonnegative := threeBlockPatternRetuneDefect_nonnegative
    sourceLaw targetLaw htargetPos
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos)
    heventLe hdefectNonnegative
  exact Q'.le_trans' _ _ _ hscaled
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (threeBlockPatternRetuneDefect
            sourceLaw targetLaw htargetPos))))

#print axioms listQSum_le_termwise
#print axioms patternRetunedEventMass_lower_bound_of_relativeEnvelope
#print axioms patternRetunedEventMass_upper_bound_of_relativeEnvelope
#print axioms patternRetunedEventMass_bounds_by_derivedDefect
#print axioms one_add_mul_add_neg_self_eqv
#print axioms one_add_neg_mul_add_neg_self_eqv
#print axioms patternRetunedEventMass_abs_sub_le_scaledDefect
#print axioms patternRetunedEventMass_abs_sub_le_derivedDefect

end YMGap.Continuum.Z4ThreeBlockPatternRetuneEventDefect
