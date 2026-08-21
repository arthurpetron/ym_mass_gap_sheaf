/-
# The finite physical BF4 Markov action recoded in cutoff-independent syntax

The finite physical Markov kernel depends on the Peter--Weyl cutoff, while the
cutoff-removed carrier is built from a cutoff-independent finite-linear
syntax.  This file supplies the missing type-level recoding: at every cutoff,
the Markov image of a unit observable is constructively clamped to the unit
interval.  The clamp is equivalent to the genuine image on every retained
physical state.  Recursion then gives an endomorphism of the same
finite-linear syntax.

On every retained state its value is exactly the genuine finite physical
Markov action, modulo rational representation.  Consequently its limiting
distance evaluated at that same cutoff obeys the exact finite Markov
contraction.  This does not yet prove that the cutoff-indexed images form a
Cauchy sequence in the limiting seminorm; that is the next analytic bridge
needed to construct one cutoff-independent completed transfer.

## Axiom gate

Only finite list sums, rational order, the genuine physical conditional
kernel, and the already proved finite/completed GNS bridges are used.  There
is no classical choice, noncomputable declaration, custom axiom, or unproved
placeholder.
-/

import YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
import YMGap.Continuum.Z4FiniteCylinderQuadraticStability

namespace YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm
open YMGap.Continuum.BF4PhysicalCutoffLinearGNSForm.CentralPhysicalLinearObservable
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletion
open YMGap.Continuum.BF4PhysicalCutoffLinearCompletedVacuumComplement
open YMGap.Continuum.BF4PhysicalCutoffStationaryBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A constructively clamped unit-interval Markov image -/

/-- Constructive rational clamp to the closed unit interval. -/
def physicalUnitClamp (value : Q') : Q' :=
  if value <= 0 then 0 else if 1 <= value then 1 else value

theorem physicalUnitClamp_nonnegative (value : Q') :
    (0 : Q') <= physicalUnitClamp value := by
  unfold physicalUnitClamp
  split
  · exact Q'.le_refl' 0
  · split
    · exact Q'.zero_le_one
    · exact Q'.le_of_lt (Int.lt_of_not_ge (by assumption))

theorem physicalUnitClamp_le_one (value : Q') :
    physicalUnitClamp value <= (1 : Q') := by
  unfold physicalUnitClamp
  split
  · exact Q'.zero_le_one
  · split
    · exact Q'.le_refl' 1
    · exact Q'.le_of_lt (Int.lt_of_not_ge (by assumption))

private theorem q_eqv_of_le_le {left right : Q'}
    (hleft : left <= right) (hright : right <= left) : left ≈ right :=
  Int.le_antisymm hleft hright

theorem physicalUnitClamp_equiv_of_bounds
    (value : Q') (hnonnegative : (0 : Q') <= value)
    (hle : value <= (1 : Q')) :
    physicalUnitClamp value ≈ value := by
  unfold physicalUnitClamp
  split
  · exact q_eqv_of_le_le hnonnegative (by assumption)
  · split
    · exact q_eqv_of_le_le (by assumption) hle
    · exact Q'.eqv_refl value

/-- The genuine Markov image, clamped only to provide the global `[0,1]`
carrier required by the cutoff-independent atomic syntax. -/
def centralPhysicalMarkovCutoffUnitObservable
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) :
    CentralPhysicalUnitObservable where
  value source := physicalUnitClamp
    (centralPhysicalMarkovApply
      w hw cutoff half observable.value source)
  nonnegative := fun _source => physicalUnitClamp_nonnegative _
  le_one := fun _source => physicalUnitClamp_le_one _

theorem centralPhysicalMarkovApply_unit_nonnegative
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) (source : EdgeLabelling) :
    (0 : Q') <= centralPhysicalMarkovApply
      w hw cutoff half observable.value source := by
  unfold centralPhysicalMarkovApply
  apply listQSum_nonnegative_on
  intro target _
  exact Q'.mul_nonneg _ _
    (centralPhysicalConditionalKernel_nonnegative
      hw cutoff half source target)
    (observable.nonnegative target)

theorem centralPhysicalMarkovApply_unit_le_one_of_mem
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) (source : EdgeLabelling)
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half) :
    centralPhysicalMarkovApply w hw cutoff half observable.value source <= 1 := by
  have hmono := listQSum_mono
    (fun target =>
      centralPhysicalConditionalKernel
          w hw cutoff half source target * observable.value target)
    (centralPhysicalConditionalKernel w hw cutoff half source)
    (centralPositiveHalfStates w hw cutoff half)
    (fun target _ => Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left
        (observable.value target) 1
        (centralPhysicalConditionalKernel
          w hw cutoff half source target)
        (observable.le_one target)
        (centralPhysicalConditionalKernel_nonnegative
          hw cutoff half source target))
      (Q'.le_of_eqv
        (Q'.mul_one_eqv
          (centralPhysicalConditionalKernel
            w hw cutoff half source target))))
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_of_eqv
      (centralPhysicalConditionalKernel_row_normalized hsource))

theorem centralPhysicalMarkovCutoffUnitObservable_value_of_mem
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) (source : EdgeLabelling)
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half) :
    (centralPhysicalMarkovCutoffUnitObservable
      hw cutoff half observable).value source ≈
      centralPhysicalMarkovApply
        w hw cutoff half observable.value source := by
  exact physicalUnitClamp_equiv_of_bounds _
    (centralPhysicalMarkovApply_unit_nonnegative
      hw cutoff half observable source)
    (centralPhysicalMarkovApply_unit_le_one_of_mem
      hw cutoff half observable source hsource)

/-! ## 2. The cutoff-indexed endomorphism of finite-linear syntax -/

/-- Recoding of the finite physical Markov action as an endomorphism of the
same cutoff-independent finite-linear syntax. -/
def centralPhysicalLinearMarkovCutoffAction
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat) :
    CentralPhysicalLinearObservable -> CentralPhysicalLinearObservable
  | zero => zero
  | atom observable =>
      atom (centralPhysicalMarkovCutoffUnitObservable
        hw cutoff half observable)
  | add left right =>
      add
        (centralPhysicalLinearMarkovCutoffAction hw cutoff half left)
        (centralPhysicalLinearMarkovCutoffAction hw cutoff half right)
  | smul scalar observable =>
      smul scalar
        (centralPhysicalLinearMarkovCutoffAction
          hw cutoff half observable)

theorem centralPhysicalMarkovApply_zero
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (source : EdgeLabelling) :
    centralPhysicalMarkovApply w hw cutoff half (fun _ => 0) source ≈ 0 := by
  unfold centralPhysicalMarkovApply
  exact Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun _ => Q'.mul_zero_eqv _)
      (centralPositiveHalfStates w hw cutoff half))
    (listQSum_zero _)

/-- On retained physical states, the recoded syntax evaluates to the literal
finite Markov action of the original syntax. -/
theorem centralPhysicalLinearMarkovCutoffAction_value_of_mem
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalLinearObservable)
    (source : EdgeLabelling)
    (hsource : source ∈ centralPositiveHalfStates w hw cutoff half) :
    (centralPhysicalLinearMarkovCutoffAction
      hw cutoff half observable).value source ≈
      centralPhysicalMarkovApply
        w hw cutoff half observable.value source := by
  induction observable with
  | zero =>
      exact Q'.eqv_symm
        (centralPhysicalMarkovApply_zero hw cutoff half source)
  | atom observable =>
      exact centralPhysicalMarkovCutoffUnitObservable_value_of_mem
        hw cutoff half observable source hsource
  | add left right hleft hright =>
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' hleft hright)
        (Q'.eqv_symm
          (centralPhysicalMarkovApply_add
            w hw cutoff half left.value right.value source))
  | smul scalar observable hinduction =>
      exact Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left scalar _ _ hinduction)
        (Q'.eqv_symm
          (centralPhysicalMarkovApply_smul
            w hw cutoff half scalar observable.value source))

/-- On every retained physical state, the recoded cutoff action fixes the
finite-linear vacuum modulo rational representation. -/
theorem centralPhysicalLinearMarkovCutoffAction_vacuum_value_of_mem
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat) :
    forall state : EdgeLabelling,
      state ∈ centralPositiveHalfStates w hw cutoff half ->
      (centralPhysicalLinearMarkovCutoffAction
        hw cutoff half centralPhysicalLinearVacuum).value state ≈ 1 := by
  intro state hstate
  exact Q'.eqv_trans _ _ _
    (centralPhysicalLinearMarkovCutoffAction_value_of_mem
      hw cutoff half centralPhysicalLinearVacuum state hstate)
    (centralPhysicalMarkovApply_one hstate)

/-! ## 3. Exact same-cutoff GNS bridge and contraction -/

/-- At its own cutoff, the recoded bilinear form is exactly the genuine
finite physical Markov form in both arguments. -/
theorem innerLimit_markovCutoffAction_both_approx_eqv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable) :
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).approx cutoff ≈
      centralPhysicalWeightedInner
        w (Q'.le_of_lt hw0) cutoff half
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half left.value)
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half right.value) := by
  have hstage := innerLimit_approx_eqv_stage hw0 hw1 half cutoff
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half left)
    (centralPhysicalLinearMarkovCutoffAction
      (Q'.le_of_lt hw0) cutoff half right)
  rw [centralPhysicalSmulGNS_B_eq] at hstage
  refine Q'.eqv_trans _ _ _ hstage ?_
  unfold centralPhysicalWeightedInner
  apply listQSum_congr_on
  intro source hsource
  apply Q'.mul_eqv_congr_left
    (centralPhysicalRowMarginal
      w (Q'.le_of_lt hw0) cutoff half source) _ _
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (Q'.le_of_lt hw0) cutoff half left source hsource))
    (Q'.mul_eqv_congr_left _ _ _
      (centralPhysicalLinearMarkovCutoffAction_value_of_mem
        (Q'.le_of_lt hw0) cutoff half right source hsource))

/-- The limiting squared distance of two recoded images, evaluated at the
same finite cutoff, is the literal finite physical output distance. -/
theorem physicalLinearDistSq_markovCutoffAction_approx_eqv
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable) :
    (physicalLinearDistSq hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).approx cutoff ≈
      (centralPhysicalSmulGNS
        w (Q'.le_of_lt hw0) cutoff half).toGNSData.distSqQ
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half left.value)
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half right.value) := by
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have hboth := innerLimit_markovCutoffAction_both_approx_eqv
    hw0 hw1 half cutoff (sub left right) (sub left right)
  have hsub : D.veq
      (centralPhysicalMarkovApply
        w (Q'.le_of_lt hw0) cutoff half (sub left right).value)
      (D.sub
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half left.value)
        (centralPhysicalMarkovApply
          w (Q'.le_of_lt hw0) cutoff half right.value)) := by
    intro source
    exact Q'.eqv_trans _ _ _
      (centralPhysicalMarkovApply_congr
        w (Q'.le_of_lt hw0) cutoff half
        (sub_value_equiv left right) source)
      (centralPhysicalMarkovApply_sub
        w (Q'.le_of_lt hw0) cutoff half left.value right.value source)
  change
    (innerLimit hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half (sub left right))
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half (sub left right))).approx cutoff ≈
      D.B
        (D.sub
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half left.value)
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half right.value))
        (D.sub
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half left.value)
          (centralPhysicalMarkovApply
            w (Q'.le_of_lt hw0) cutoff half right.value))
  exact Q'.eqv_trans _ _ _ hboth (D.B_diag_congr hsub)

/-- Concrete diagonal certificate: at each cutoff, the recoded action is
contractive when both limiting squared distances are evaluated at that same
cutoff. -/
theorem physicalLinearDistSq_markovCutoffAction_approx_le
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half cutoff : Nat)
    (left right : CentralPhysicalLinearObservable) :
    (physicalLinearDistSq hw0 hw1 half
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half left)
      (centralPhysicalLinearMarkovCutoffAction
        (Q'.le_of_lt hw0) cutoff half right)).approx cutoff <=
      (physicalLinearDistSq hw0 hw1 half left right).approx cutoff := by
  let D := (centralPhysicalSmulGNS
    w (Q'.le_of_lt hw0) cutoff half).toGNSData
  have houtput := physicalLinearDistSq_markovCutoffAction_approx_eqv
    hw0 hw1 half cutoff left right
  have hinput := physicalLinearDistSq_approx_eqv_stage
    hw0 hw1 half cutoff left right
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv houtput)
    (Q'.le_trans' _ _ _
      (centralPhysicalMarkovApply_distSq_contraction
        w (Q'.le_of_lt hw0) cutoff half left.value right.value)
      (Q'.ge_of_eqv hinput))

/-! ## Axiom audit -/

#print axioms centralPhysicalMarkovCutoffUnitObservable
#print axioms centralPhysicalLinearMarkovCutoffAction_value_of_mem
#print axioms centralPhysicalLinearMarkovCutoffAction_vacuum_value_of_mem
#print axioms innerLimit_markovCutoffAction_both_approx_eqv
#print axioms physicalLinearDistSq_markovCutoffAction_approx_eqv
#print axioms physicalLinearDistSq_markovCutoffAction_approx_le

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
