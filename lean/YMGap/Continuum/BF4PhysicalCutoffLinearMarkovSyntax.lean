/-
# The finite physical BF4 Markov action recoded in cutoff-independent syntax

The finite physical Markov kernel depends on the Peter--Weyl cutoff, while the
cutoff-removed carrier is built from a cutoff-independent finite-linear
syntax.  This file supplies the missing type-level recoding.  At every cutoff,
the Markov image of a unit observable is extended by the missing row mass:

`P_K f + (1 - P_K 1) f`.

The extension is globally unit-interval-valued, agrees with the genuine image
on every retained physical state, and fixes the constant-one observable on
every edge labelling.  Recursion then gives a vacuum-fixing endomorphism of
the same finite-linear syntax.

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
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. A globally stochastic unit-interval Markov extension -/

private theorem listQSum_filter_le_nonnegative_local {A : Type}
    (value : A -> Q') (test : A -> Bool)
    (hvalue : forall item, (0 : Q') <= value item) :
    forall items : List A,
      listQSum value (items.filter test) <= listQSum value items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      have ih := listQSum_filter_le_nonnegative_local
        value test hvalue tail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          have hmono : listQSum value tail <=
              value head + listQSum value tail := by
            have hscaled := Q'.add_le_add_right
              (0 : Q') (value head) (listQSum value tail)
              (hvalue head)
            rwa [Q'.zero_add'] at hscaled
          exact Q'.le_trans' _ _ _ ih hmono
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_le_add_left (value head) _ _ ih

/-- A positive conditional row sums to one on the full lower-state list,
without requiring its source to lie in that list. -/
theorem centralPhysicalConditionalKernel_full_row_equiv_one_of_pos
    {w : Q'} {hw : (0 : Q') <= w} {cutoff half : Nat}
    {source : EdgeLabelling}
    (hrow : (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half source) :
    listQSum
        (centralPhysicalConditionalKernel
          w hw cutoff half source)
        (centralHalfStates cutoff half) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        Q'.divPos
          (centralNormalizedPhysicalReflectedKernel
            w hw cutoff half source target)
          (centralPhysicalRowMarginal
            w hw cutoff half source)
          hrow)
      (centralHalfStates cutoff half)) _ ?_ ?_
  · apply listQSum_congr
    intro target
    exact Q'.eqv_of_eq
      (centralPhysicalConditionalKernel_eq_divPos
        (target := target) hrow)
  · unfold Q'.divPos centralPhysicalRowMarginal
    exact Q'.eqv_trans _ _ _
      (listQSum_mul_right
        (centralNormalizedPhysicalReflectedKernel
          w hw cutoff half source)
        (Q'.recipPos
          (listQSum
            (centralNormalizedPhysicalReflectedKernel
              w hw cutoff half source)
            (centralHalfStates cutoff half))
          hrow)
        (centralHalfStates cutoff half))
      (Q'.mul_recipPos_eqv _ hrow)

/-- Every conditional row has retained mass at most one, including sources
outside the retained carrier. -/
theorem centralPhysicalConditionalKernel_retained_row_le_one
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (source : EdgeLabelling) :
    listQSum
        (centralPhysicalConditionalKernel
          w hw cutoff half source)
        (centralPositiveHalfStates w hw cutoff half) <= 1 := by
  have hfilter :
      listQSum
          (centralPhysicalConditionalKernel
            w hw cutoff half source)
          (centralPositiveHalfStates w hw cutoff half) <=
        listQSum
          (centralPhysicalConditionalKernel
            w hw cutoff half source)
          (centralHalfStates cutoff half) := by
    unfold centralPositiveHalfStates
    exact listQSum_filter_le_nonnegative_local
      (centralPhysicalConditionalKernel
        w hw cutoff half source)
      (fun target => decide ((0 : Q') <
        centralPhysicalRowMarginal w hw cutoff half target))
      (fun target =>
        centralPhysicalConditionalKernel_nonnegative
          hw cutoff half source target)
      (centralHalfStates cutoff half)
  refine Q'.le_trans' _ _ _ hfilter ?_
  by_cases hrow : (0 : Q') <
      centralPhysicalRowMarginal w hw cutoff half source
  · exact Q'.le_of_eqv
      (centralPhysicalConditionalKernel_full_row_equiv_one_of_pos hrow)
  · refine Q'.le_trans' _ 0 1 (Q'.le_of_eqv ?_) Q'.zero_le_one
    refine Q'.eqv_trans _
      (listQSum (fun _ : EdgeLabelling => 0)
        (centralHalfStates cutoff half)) _ ?_ (listQSum_zero _)
    apply listQSum_congr
    intro target
    unfold centralPhysicalConditionalKernel
    rw [dif_neg hrow]
    exact Q'.eqv_refl 0

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

/-- The image of a unit observable is bounded above by the retained row
mass, even when the source itself is not retained. -/
theorem centralPhysicalMarkovApply_unit_le_row_mass
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) (source : EdgeLabelling) :
    centralPhysicalMarkovApply
        w hw cutoff half observable.value source <=
      centralPhysicalMarkovApply
        w hw cutoff half (fun _ => 1) source := by
  unfold centralPhysicalMarkovApply
  exact listQSum_mono
    (fun target =>
      centralPhysicalConditionalKernel
          w hw cutoff half source target * observable.value target)
    (fun target =>
      centralPhysicalConditionalKernel
          w hw cutoff half source target * 1)
    (centralPositiveHalfStates w hw cutoff half)
    (fun target _ =>
      Q'.mul_le_mul_of_nonneg_left
        (observable.value target) 1
        (centralPhysicalConditionalKernel
          w hw cutoff half source target)
        (observable.le_one target)
        (centralPhysicalConditionalKernel_nonnegative
          hw cutoff half source target))

/-- The retained row mass `P_K 1` is globally at most one. -/
theorem centralPhysicalMarkovApply_one_le_one
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (source : EdgeLabelling) :
    centralPhysicalMarkovApply
        w hw cutoff half (fun _ => 1) source <= 1 := by
  unfold centralPhysicalMarkovApply
  refine Q'.le_trans' _
    (listQSum
      (centralPhysicalConditionalKernel
        w hw cutoff half source)
      (centralPositiveHalfStates w hw cutoff half)) _ ?_ ?_
  · exact Q'.le_of_eqv
      (listQSum_congr
        (fun target => Q'.mul_one_eqv
          (centralPhysicalConditionalKernel
            w hw cutoff half source target))
        (centralPositiveHalfStates w hw cutoff half))
  · exact centralPhysicalConditionalKernel_retained_row_le_one
      hw cutoff half source

private theorem row_plus_missing_mass_equiv_one (rowMass : Q') :
    rowMass + (1 + -rowMass) * 1 ≈ 1 := by
  refine Q'.eqv_trans _ (rowMass + (1 + -rowMass)) _
    (Q'.add_eqv_congr_left rowMass _ _
      (Q'.mul_one_eqv (1 + -rowMass))) ?_
  refine Q'.eqv_trans _ (rowMass + (-rowMass + 1)) _
    (Q'.add_eqv_congr_left rowMass _ _
      (Q'.add_comm_eqv 1 (-rowMass))) ?_
  refine Q'.eqv_trans _ ((rowMass + -rowMass) + 1) _
    (Q'.eqv_symm (Q'.add_assoc_eqv rowMass (-rowMass) 1)) ?_
  refine Q'.eqv_trans _ (0 + 1) _
    (Q'.add_eqv_congr_right _ 0 1
      (Q'.add_neg_self_eqv rowMass)) ?_
  exact Q'.eqv_of_eq (Q'.zero_add' 1)

/-- The genuine retained-row Markov image, extended outside normalized rows
by the missing row mass.  This formula is constructive, globally takes values
in `[0,1]`, agrees with the genuine image on retained sources, and fixes the
constant-one observable globally. -/
def centralPhysicalMarkovCutoffUnitObservable
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (observable : CentralPhysicalUnitObservable) :
    CentralPhysicalUnitObservable where
  value source :=
    centralPhysicalMarkovApply
        w hw cutoff half observable.value source +
      (1 + -centralPhysicalMarkovApply
        w hw cutoff half (fun _ => 1) source) *
      observable.value source
  nonnegative := by
    intro source
    exact Q'.zero_le_add _ _
      (centralPhysicalMarkovApply_unit_nonnegative
        hw cutoff half observable source)
      (Q'.mul_nonneg _ _
        (Q'.sub_nonneg_of_le
          (centralPhysicalMarkovApply_one_le_one
            hw cutoff half source))
        (observable.nonnegative source))
  le_one := by
    intro source
    let raw := centralPhysicalMarkovApply
      w hw cutoff half observable.value source
    let rowMass := centralPhysicalMarkovApply
      w hw cutoff half (fun _ => 1) source
    let missing := 1 + -rowMass
    have hraw : raw <= rowMass :=
      centralPhysicalMarkovApply_unit_le_row_mass
        hw cutoff half observable source
    have hmissing : (0 : Q') <= missing :=
      Q'.sub_nonneg_of_le
        (centralPhysicalMarkovApply_one_le_one
          hw cutoff half source)
    have hscaled : missing * observable.value source <= missing * 1 :=
      Q'.mul_le_mul_of_nonneg_left
        (observable.value source) 1 missing
        (observable.le_one source) hmissing
    exact Q'.le_trans' _ (rowMass + missing * 1) _
      (Q'.add_le_add hraw hscaled)
      (Q'.le_of_eqv (row_plus_missing_mass_equiv_one rowMass))

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
  let raw := centralPhysicalMarkovApply
    w hw cutoff half observable.value source
  let rowMass := centralPhysicalMarkovApply
    w hw cutoff half (fun _ => 1) source
  have hrow : rowMass ≈ 1 := centralPhysicalMarkovApply_one hsource
  have hmissing : 1 + -rowMass ≈ 0 :=
    Q'.eqv_trans _ (1 + -1) _
      (Q'.add_eqv_congr_left 1 (-rowMass) (-1)
        (Q'.neg_eqv_congr rowMass 1 hrow))
      (Q'.add_neg_self_eqv 1)
  have hcorrection : (1 + -rowMass) * observable.value source ≈ 0 :=
    Q'.eqv_trans _ (0 * observable.value source) _
      (Q'.mul_eqv_congr_right
        (1 + -rowMass) 0 (observable.value source) hmissing)
      (Q'.zero_mul_eqv _)
  exact Q'.eqv_trans _ (raw + 0) _
    (Q'.add_eqv_congr_left raw _ 0 hcorrection)
    (Q'.eqv_of_eq (Q'.add_zero' raw))

/-- The atomic cutoff recoding fixes the constant-one unit observable on
every edge labelling, not merely on its retained source carrier. -/
theorem centralPhysicalMarkovCutoffUnitObservable_one_value
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (source : EdgeLabelling) :
    (centralPhysicalMarkovCutoffUnitObservable
      hw cutoff half centralPhysicalUnitObservable).value source ≈ 1 := by
  exact row_plus_missing_mass_equiv_one
    (centralPhysicalMarkovApply
      w hw cutoff half (fun _ => 1) source)

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

/-- The recoded cutoff action fixes the finite-linear vacuum globally. -/
theorem centralPhysicalLinearMarkovCutoffAction_vacuum_value
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat)
    (state : EdgeLabelling) :
    (centralPhysicalLinearMarkovCutoffAction
      hw cutoff half centralPhysicalLinearVacuum).value state ≈ 1 := by
  exact centralPhysicalMarkovCutoffUnitObservable_one_value
    hw cutoff half state

/-- The cutoff action fixes the vacuum as a semantic finite-linear object. -/
theorem centralPhysicalLinearMarkovCutoffAction_vacuum_equivalent
    {w : Q'} (hw : (0 : Q') <= w) (cutoff half : Nat) :
    Equivalent
      (centralPhysicalLinearMarkovCutoffAction
        hw cutoff half centralPhysicalLinearVacuum)
      centralPhysicalLinearVacuum := by
  intro state
  exact centralPhysicalLinearMarkovCutoffAction_vacuum_value
    hw cutoff half state

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
#print axioms centralPhysicalConditionalKernel_retained_row_le_one
#print axioms centralPhysicalLinearMarkovCutoffAction_value_of_mem
#print axioms centralPhysicalLinearMarkovCutoffAction_vacuum_equivalent
#print axioms innerLimit_markovCutoffAction_both_approx_eqv
#print axioms physicalLinearDistSq_markovCutoffAction_approx_eqv
#print axioms physicalLinearDistSq_markovCutoffAction_approx_le

end YMGap.Continuum.BF4PhysicalCutoffLinearMarkovSyntax
