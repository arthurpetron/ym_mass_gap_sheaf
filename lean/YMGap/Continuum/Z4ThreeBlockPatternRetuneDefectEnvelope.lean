/-
# Exact defect envelopes for three-block pattern retuning

The eight rational retune ratios become useful in a scale recursion only after
they are equipped with certified bounds.  This module supplies two bridges:

* relative lower/upper cell-mass comparisons give the same lower/upper bounds
  on every ratio and hence pointwise bounds on the retuned target law;
* an absolute cross-difference estimate gives an absolute ratio-minus-one
  estimate, and the maximum over the eight Boolean cells is itself an exact,
  derived rational defect.

The resulting defect is finite and normalization-safe by construction.  Its
smallness or summability for physical successive-scale laws remains a separate
analytic obligation.
-/

import YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio
import YMGap.Continuum.FusionQuotientCollapse

namespace YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeBlockOverlapCumulantKernel
open YMGap.Continuum.Z4ThreeBlockPatternRetunedLaw
open YMGap.Continuum.Z4ThreeBlockPatternRetuneRatio

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Cross-difference control of one exact ratio -/

theorem patternRetuneRatio_abs_sub_one_le_of_crossDiff
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) (bound : Q')
    (hcross :
      absQ
          (threeBlockPatternMass sourceLaw pattern +
            -threeBlockPatternMass targetLaw pattern) ≤
        bound * threeBlockPatternMass targetLaw pattern) :
    absQ
        (patternRetuneRatio sourceLaw targetLaw htargetPos pattern +
          -(1 : Q')) ≤ bound := by
  exact absQ_divPos_sub_one_le (htargetPos pattern) hcross

/-! ## 2. Relative cell envelopes transport to ratios and atoms -/

structure ThreeBlockPatternRelativeEnvelope {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (lower upper : Q') : Prop where
  lower_cell : ∀ pattern,
    lower * threeBlockPatternMass targetLaw pattern ≤
      threeBlockPatternMass sourceLaw pattern
  upper_cell : ∀ pattern,
    threeBlockPatternMass sourceLaw pattern ≤
      upper * threeBlockPatternMass targetLaw pattern

theorem patternRetuneRatio_bounds_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (pattern : ThreeBlockPattern) :
    lower ≤ patternRetuneRatio
        sourceLaw targetLaw htargetPos pattern ∧
      patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≤ upper := by
  exact ⟨Q'.le_divPos_of_mul_le _ _ (htargetPos pattern)
      (envelope.lower_cell pattern),
    Q'.divPos_le_of_le_mul _ _ (htargetPos pattern)
      (envelope.upper_cell pattern)⟩

theorem patternRetunedTargetMass_lower_bound_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (target : Target) :
    lower * targetLaw.mass target ≤
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target := by
  have hratio :=
    (patternRetuneRatio_bounds_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope
      (threeBlockPattern targetLaw target)).1
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (targetLaw.mass target) hratio (targetLaw.mass_nonnegative target)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.mul_comm_eqv lower (targetLaw.mass target)))
    (Q'.le_trans' _ _ _ hmul
      (Q'.ge_of_eqv
        (patternRetunedTargetMass_eqv_targetMass_mul_ratio
          sourceLaw targetLaw htargetPos target)))

theorem patternRetunedTargetMass_upper_bound_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (target : Target) :
    patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≤
      upper * targetLaw.mass target := by
  have hratio :=
    (patternRetuneRatio_bounds_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope
      (threeBlockPattern targetLaw target)).2
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _
    (targetLaw.mass target) hratio (targetLaw.mass_nonnegative target)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (patternRetunedTargetMass_eqv_targetMass_mul_ratio
        sourceLaw targetLaw htargetPos target))
    (Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv (targetLaw.mass target) upper)))

theorem patternRetunedTargetMass_bounds_of_relativeEnvelope
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    {lower upper : Q'}
    (envelope : ThreeBlockPatternRelativeEnvelope
      sourceLaw targetLaw lower upper)
    (target : Target) :
    lower * targetLaw.mass target ≤
        patternRetunedTargetMass sourceLaw targetLaw htargetPos target ∧
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≤
        upper * targetLaw.mass target := by
  exact ⟨patternRetunedTargetMass_lower_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope target,
    patternRetunedTargetMass_upper_bound_of_relativeEnvelope
      sourceLaw targetLaw htargetPos envelope target⟩

/-! ## 3. A finite maximum over exactly eight cells -/

def qMax8 (a0 a1 a2 a3 a4 a5 a6 a7 : Q') : Q' :=
  Q'.max' a0
    (Q'.max' a1
      (Q'.max' a2
        (Q'.max' a3
          (Q'.max' a4
            (Q'.max' a5 (Q'.max' a6 a7))))))

theorem qMax8_bounds (a0 a1 a2 a3 a4 a5 a6 a7 : Q') :
    a0 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a1 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a2 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a3 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a4 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a5 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a6 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ∧
    a7 ≤ qMax8 a0 a1 a2 a3 a4 a5 a6 a7 := by
  unfold qMax8
  constructor
  · exact Q'.le_max'_left _ _
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_max'_right _ _)
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_max'_right _ _))
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
          (Q'.le_max'_right _ _)))
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
          (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
            (Q'.le_max'_right _ _))))
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
          (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
            (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
              (Q'.le_max'_right _ _)))))
  constructor
  · exact Q'.le_trans' _ _ _ (Q'.le_max'_left _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
          (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
            (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
              (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
                (Q'.le_max'_right _ _))))))
  exact Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
    (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
      (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
        (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
          (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
            (Q'.le_trans' _ _ _ (Q'.le_max'_right _ _)
              (Q'.le_max'_right _ _))))))

theorem qMax8_le_of_bounds {a0 a1 a2 a3 a4 a5 a6 a7 bound : Q'}
    (h0 : a0 ≤ bound) (h1 : a1 ≤ bound)
    (h2 : a2 ≤ bound) (h3 : a3 ≤ bound)
    (h4 : a4 ≤ bound) (h5 : a5 ≤ bound)
    (h6 : a6 ≤ bound) (h7 : a7 ≤ bound) :
    qMax8 a0 a1 a2 a3 a4 a5 a6 a7 ≤ bound := by
  unfold qMax8
  exact (Q'.max'_le_iff' _ _ bound).mpr ⟨h0,
    (Q'.max'_le_iff' _ _ bound).mpr ⟨h1,
      (Q'.max'_le_iff' _ _ bound).mpr ⟨h2,
        (Q'.max'_le_iff' _ _ bound).mpr ⟨h3,
          (Q'.max'_le_iff' _ _ bound).mpr ⟨h4,
            (Q'.max'_le_iff' _ _ bound).mpr ⟨h5,
              (Q'.max'_le_iff' _ _ bound).mpr ⟨h6, h7⟩⟩⟩⟩⟩⟩⟩

def patternRetuneRelativeError {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) : Q' :=
  absQ
    (patternRetuneRatio sourceLaw targetLaw htargetPos pattern +
      -(1 : Q'))

def threeBlockPatternRetuneDefect {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) : Q' :=
  qMax8
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, false, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, false, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, true, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, true, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, false, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, false, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, true, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, true, true))

theorem patternRetuneRelativeError_le_defect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    patternRetuneRelativeError sourceLaw targetLaw htargetPos pattern ≤
      threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos := by
  obtain ⟨left, ⟨shared, right⟩⟩ := pattern
  have hall := qMax8_bounds
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, false, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, false, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, true, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (false, true, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, false, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, false, true))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, true, false))
    (patternRetuneRelativeError sourceLaw targetLaw htargetPos
      (true, true, true))
  cases left <;> cases shared <;> cases right
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2.1
  · exact hall.2.2.2.2.1
  · exact hall.2.2.2.2.2.1
  · exact hall.2.2.2.2.2.2.1
  · exact hall.2.2.2.2.2.2.2

theorem threeBlockPatternRetuneDefect_nonnegative
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    (0 : Q') ≤ threeBlockPatternRetuneDefect
      sourceLaw targetLaw htargetPos := by
  exact Q'.le_trans' _ _ _
    (absQ_nonneg
      (patternRetuneRatio sourceLaw targetLaw htargetPos
        (false, false, false) + -(1 : Q')))
    (patternRetuneRelativeError_le_defect sourceLaw targetLaw htargetPos
      (false, false, false))

theorem one_add_neg_le_of_absQ_sub_one_le {ratio defect : Q'}
    (habs : absQ (ratio + -(1 : Q')) ≤ defect) :
    (1 : Q') + -defect ≤ ratio := by
  have hlower : -defect ≤ ratio + -(1 : Q') := by
    refine Q'.le_trans' _ _ _ (Q'.neg_le_neg habs) ?_
    exact neg_absQ_le (ratio + -(1 : Q'))
  have hstep := Q'.add_le_add_right _ _ (1 : Q') hlower
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.add_comm_eqv (1 : Q') (-defect))) ?_
  refine Q'.le_trans' _ _ _ hstep (Q'.le_of_eqv ?_)
  refine Q'.eqv_trans _ _ _
    (Q'.add_assoc_eqv ratio (-(1 : Q')) (1 : Q')) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left ratio _ _
      (Q'.neg_add_self_eqv (1 : Q'))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' ratio)

theorem le_one_add_of_absQ_sub_one_le {ratio defect : Q'}
    (habs : absQ (ratio + -(1 : Q')) ≤ defect) :
    ratio ≤ (1 : Q') + defect := by
  have hupper : ratio + -(1 : Q') ≤ defect :=
    Q'.le_trans' _ _ _ (le_absQ (ratio + -(1 : Q'))) habs
  have hstep := Q'.add_le_add_right _ _ (1 : Q') hupper
  have hcollapse :
      (ratio + -(1 : Q')) + (1 : Q') ≈ ratio := by
    refine Q'.eqv_trans _ _ _
      (Q'.add_assoc_eqv ratio (-(1 : Q')) (1 : Q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.add_eqv_congr_left ratio _ _
        (Q'.neg_add_self_eqv (1 : Q'))) ?_
    exact Q'.eqv_of_eq (Q'.add_zero' ratio)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hcollapse)
    (Q'.le_trans' _ _ _ hstep
      (Q'.le_of_eqv (Q'.add_comm_eqv defect (1 : Q'))))

theorem patternRetuneRatio_bounds_by_derivedDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (pattern : ThreeBlockPattern) :
    (1 : Q') + -threeBlockPatternRetuneDefect
          sourceLaw targetLaw htargetPos ≤
        patternRetuneRatio sourceLaw targetLaw htargetPos pattern ∧
      patternRetuneRatio sourceLaw targetLaw htargetPos pattern ≤
        (1 : Q') + threeBlockPatternRetuneDefect
          sourceLaw targetLaw htargetPos := by
  have habs := patternRetuneRelativeError_le_defect
    sourceLaw targetLaw htargetPos pattern
  exact ⟨one_add_neg_le_of_absQ_sub_one_le habs,
    le_one_add_of_absQ_sub_one_le habs⟩

def derivedDefectRelativeEnvelope {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern) :
    ThreeBlockPatternRelativeEnvelope sourceLaw targetLaw
      ((1 : Q') + -threeBlockPatternRetuneDefect
        sourceLaw targetLaw htargetPos)
      ((1 : Q') + threeBlockPatternRetuneDefect
        sourceLaw targetLaw htargetPos) where
  lower_cell := by
    intro pattern
    have hratio :=
      (patternRetuneRatio_bounds_by_derivedDefect
        sourceLaw targetLaw htargetPos pattern).1
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _
      (threeBlockPatternMass targetLaw pattern) hratio
      (Q'.le_of_lt (htargetPos pattern))
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (patternRetuneRatio_mul_targetPatternMass
          sourceLaw targetLaw htargetPos pattern))
  upper_cell := by
    intro pattern
    have hratio :=
      (patternRetuneRatio_bounds_by_derivedDefect
        sourceLaw targetLaw htargetPos pattern).2
    have hmul := Q'.mul_le_mul_of_nonneg_right _ _
      (threeBlockPatternMass targetLaw pattern) hratio
      (Q'.le_of_lt (htargetPos pattern))
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (patternRetuneRatio_mul_targetPatternMass
          sourceLaw targetLaw htargetPos pattern)) hmul

theorem patternRetunedTargetMass_bounds_by_derivedDefect
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (target : Target) :
    ((1 : Q') + -threeBlockPatternRetuneDefect
        sourceLaw targetLaw htargetPos) * targetLaw.mass target ≤
        patternRetunedTargetMass sourceLaw targetLaw htargetPos target ∧
      patternRetunedTargetMass sourceLaw targetLaw htargetPos target ≤
        ((1 : Q') + threeBlockPatternRetuneDefect
          sourceLaw targetLaw htargetPos) * targetLaw.mass target := by
  exact patternRetunedTargetMass_bounds_of_relativeEnvelope
    sourceLaw targetLaw htargetPos
    (derivedDefectRelativeEnvelope sourceLaw targetLaw htargetPos) target

theorem threeBlockPatternRetuneDefect_le_of_crossDiff
    {Source Target : Type}
    (sourceLaw : ThreeBlockOverlapFiniteLaw Source)
    (targetLaw : ThreeBlockOverlapFiniteLaw Target)
    (htargetPos : ∀ pattern,
      (0 : Q') < threeBlockPatternMass targetLaw pattern)
    (bound : Q')
    (hcross : ∀ pattern,
      absQ
          (threeBlockPatternMass sourceLaw pattern +
            -threeBlockPatternMass targetLaw pattern) ≤
        bound * threeBlockPatternMass targetLaw pattern) :
    threeBlockPatternRetuneDefect sourceLaw targetLaw htargetPos ≤ bound := by
  unfold threeBlockPatternRetuneDefect
  apply qMax8_le_of_bounds
  all_goals
    unfold patternRetuneRelativeError
    apply patternRetuneRatio_abs_sub_one_le_of_crossDiff
    exact hcross _

#print axioms patternRetuneRatio_abs_sub_one_le_of_crossDiff
#print axioms patternRetuneRatio_bounds_of_relativeEnvelope
#print axioms patternRetunedTargetMass_bounds_of_relativeEnvelope
#print axioms qMax8_bounds
#print axioms qMax8_le_of_bounds
#print axioms patternRetuneRelativeError_le_defect
#print axioms threeBlockPatternRetuneDefect_nonnegative
#print axioms one_add_neg_le_of_absQ_sub_one_le
#print axioms le_one_add_of_absQ_sub_one_le
#print axioms patternRetuneRatio_bounds_by_derivedDefect
#print axioms derivedDefectRelativeEnvelope
#print axioms patternRetunedTargetMass_bounds_by_derivedDefect
#print axioms threeBlockPatternRetuneDefect_le_of_crossDiff

end YMGap.Continuum.Z4ThreeBlockPatternRetuneDefectEnvelope
