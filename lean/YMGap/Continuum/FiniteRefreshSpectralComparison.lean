/-
# Proof-carrying finite comparison with a refresh operator

An exact finite computation can compare a candidate Markov kernel with a
reference refresh kernel by bounding, row by row, the `L1` norm of their
difference.  If the reference kills a centered observable and that observable
is bounded by `M`, then the candidate action is bounded by `epsilon * M`.
Thus `epsilon < 1` supplies the explicit positive contraction margin
`1 - epsilon`.

The certificate is suitable for external exact arithmetic, interval code, or
finite statistical bounds: those tools may propose `epsilon`, but Lean checks
the row-defect inequality and all deductions.  This is a finite contraction
theorem, not by itself a cutoff-uniform spectral gap or a continuum theorem.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.FiniteSignedKernelL1

namespace YMGap.Continuum.FiniteRefreshSpectralComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Finite observable actions and exact row defects -/

def finiteObservableAction
    {Source Target : Type}
    (targets : List Target)
    (kernel : Source → Target → Q')
    (observable : Target → Q')
    (source : Source) : Q' :=
  listQSum
    (fun target => kernel source target * observable target)
    targets

def finiteKernelDifferenceAction
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q')
    (source : Source) : Q' :=
  listQSum
    (fun target =>
      (kernel source target + (-reference source target)) *
        observable target)
    targets

def finiteRowL1Defect
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (source : Source) : Q' :=
  finiteL1Norm targets
    (fun target => kernel source target + (-reference source target))

private theorem listQSum_neg_local
    {A : Type} (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      unfold listQSum
      refine Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr_left (-(value head)) _ _
          (listQSum_neg_local value tail)) ?_
      exact Q'.eqv_symm
        (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem abs_listQSum_le_sum_abs_local
    {A : Type} (value : A → Q') : ∀ items : List A,
    Q'.abs (listQSum value items) ≤
      listQSum (fun item => Q'.abs (value item)) items
  | [] => by
      change Q'.abs (0 : Q') ≤ 0
      decide
  | head :: tail => by
      change
        Q'.abs (value head + listQSum value tail) ≤
          Q'.abs (value head) +
            listQSum (fun item => Q'.abs (value item)) tail
      exact Q'.le_trans' _ _ _
        (abs_add_le (value head) (listQSum value tail))
        (Q'.add_le_add_left _ _ _
          (abs_listQSum_le_sum_abs_local value tail))

/-- A pointwise exact equality makes the finite row defect exactly zero. -/
theorem finiteRowL1Defect_eqv_zero_of_pointwise
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (source : Source)
    (pointwise :
      ∀ target, target ∈ targets →
        kernel source target ≈ reference source target) :
    finiteRowL1Defect targets kernel reference source ≈ 0 := by
  unfold finiteRowL1Defect finiteL1Norm
  refine Q'.eqv_trans _
    (listQSum (fun _ => (0 : Q')) targets) _ ?_ ?_
  · apply listQSum_congr_on
    intro target htarget
    refine Q'.eqv_trans _ (Q'.abs 0) _ ?_ (by decide)
    exact Q'.abs_eqv_congr
      (Q'.eqv_trans _
        (reference source target + (-reference source target)) _
        (Q'.add_eqv_congr_right _ _ _
          (pointwise target htarget))
        (Q'.add_neg_self_eqv _))
  exact listQSum_zero targets

/-! ## 2. The finite comparison estimate -/

theorem finiteKernelDifferenceAction_abs_le
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q')
    (source : Source) (bound epsilon : Q')
    (bound_nonnegative : (0 : Q') ≤ bound)
    (observable_bound :
      ∀ target, target ∈ targets →
        Q'.abs (observable target) ≤ bound)
    (row_defect_le :
      finiteRowL1Defect targets kernel reference source ≤ epsilon) :
    Q'.abs
        (finiteKernelDifferenceAction
          targets kernel reference observable source) ≤
      epsilon * bound := by
  let difference := fun target =>
    kernel source target + (-reference source target)
  have htriangle :
      Q'.abs
          (finiteKernelDifferenceAction
            targets kernel reference observable source) ≤
        listQSum
          (fun target => Q'.abs (difference target * observable target))
          targets := by
    unfold finiteKernelDifferenceAction difference
    exact abs_listQSum_le_sum_abs_local _ targets
  have hpointwise :
      listQSum
          (fun target => Q'.abs (difference target * observable target))
          targets ≤
        listQSum
          (fun target => Q'.abs (difference target) * bound)
          targets := by
    apply listQSum_mono
    intro target htarget
    exact Q'.le_trans' _ _ _
      (abs_mul_le (difference target) (observable target))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (observable_bound target htarget)
        (Q'.abs_nonneg (difference target)))
  have hfactor :
      listQSum
          (fun target => Q'.abs (difference target) * bound)
          targets ≈
        finiteRowL1Defect targets kernel reference source * bound := by
    unfold finiteRowL1Defect finiteL1Norm difference
    exact listQSum_mul_right _ bound targets
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.le_trans' _ _ _ hpointwise
      (Q'.le_trans' _ _ _
        (Q'.le_of_eqv hfactor)
        (Q'.mul_le_mul_of_nonneg_right _ _ _
          row_defect_le bound_nonnegative)))

/-- If the reference action vanishes, the candidate action is exactly the
signed difference action. -/
theorem finiteObservableAction_eqv_difference_of_reference_zero
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q')
    (source : Source)
    (reference_zero :
      finiteObservableAction targets reference observable source ≈ 0) :
    finiteObservableAction targets kernel observable source ≈
      finiteKernelDifferenceAction
        targets kernel reference observable source := by
  refine Q'.eqv_symm (Q'.eqv_trans _
    (finiteObservableAction targets kernel observable source +
      (-finiteObservableAction targets reference observable source)) _ ?_ ?_)
  · unfold finiteKernelDifferenceAction finiteObservableAction
    refine Q'.eqv_trans _
      (listQSum
        (fun target =>
          kernel source target * observable target +
            (-(reference source target * observable target)))
        targets) _ ?_ ?_
    · apply listQSum_congr
      intro target
      q_ring
    refine Q'.eqv_trans _
      (listQSum
          (fun target => kernel source target * observable target) targets +
        listQSum
          (fun target =>
            -(reference source target * observable target)) targets) _
      (listQSum_add _ _ targets) ?_
    exact Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (listQSum_neg_local
        (fun target => reference source target * observable target)
        targets)
  refine Q'.eqv_trans _
    (finiteObservableAction targets kernel observable source + (-0)) _
    (Q'.add_eqv_congr'
      (Q'.eqv_refl _)
      (Q'.neg_eqv_congr _ _ reference_zero)) ?_
  refine Q'.eqv_trans _
    (finiteObservableAction targets kernel observable source + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (by decide)) ?_
  exact QPoly.q_add_zero_eqv _

/-- Main checked comparison: a centered reference action and an exact row
`L1` defect bound control the candidate centered action. -/
theorem finiteObservableAction_centered_abs_le
    {Source Target : Type}
    (targets : List Target)
    (kernel reference : Source → Target → Q')
    (observable : Target → Q')
    (source : Source) (bound epsilon : Q')
    (bound_nonnegative : (0 : Q') ≤ bound)
    (observable_bound :
      ∀ target, target ∈ targets →
        Q'.abs (observable target) ≤ bound)
    (reference_zero :
      finiteObservableAction targets reference observable source ≈ 0)
    (row_defect_le :
      finiteRowL1Defect targets kernel reference source ≤ epsilon) :
    Q'.abs (finiteObservableAction targets kernel observable source) ≤
      epsilon * bound := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (finiteObservableAction_eqv_difference_of_reference_zero
          targets kernel reference observable source reference_zero)))
    (finiteKernelDifferenceAction_abs_le
      targets kernel reference observable source bound epsilon
      bound_nonnegative observable_bound row_defect_le)

/-! ## 3. Proof-carrying Markov comparison packet -/

structure FiniteRefreshComparisonCertificate
    {State : Type}
    (states : List State)
    (kernel reference : State → State → Q') : Type where
  epsilon : Q'
  epsilon_nonnegative : (0 : Q') ≤ epsilon
  epsilon_lt_one : epsilon < (1 : Q')
  kernel_nonnegative :
    ∀ source, source ∈ states →
      ∀ target, target ∈ states →
        (0 : Q') ≤ kernel source target
  kernel_row_normalized :
    ∀ source, source ∈ states →
      listQSum (kernel source) states ≈ 1
  reference_nonnegative :
    ∀ source, source ∈ states →
      ∀ target, target ∈ states →
        (0 : Q') ≤ reference source target
  reference_row_normalized :
    ∀ source, source ∈ states →
      listQSum (reference source) states ≈ 1
  row_defect_le :
    ∀ source, source ∈ states →
      finiteRowL1Defect states kernel reference source ≤ epsilon

namespace FiniteRefreshComparisonCertificate

def contractionMargin
    {State : Type} {states : List State}
    {kernel reference : State → State → Q'}
    (certificate :
      FiniteRefreshComparisonCertificate states kernel reference) : Q' :=
  (1 : Q') - certificate.epsilon

theorem contractionMargin_pos
    {State : Type} {states : List State}
    {kernel reference : State → State → Q'}
    (certificate :
      FiniteRefreshComparisonCertificate states kernel reference) :
    (0 : Q') < certificate.contractionMargin := by
  exact one_sub_pos_of_lt_one certificate.epsilon_lt_one

theorem centeredAction_abs_le
    {State : Type} {states : List State}
    {kernel reference : State → State → Q'}
    (certificate :
      FiniteRefreshComparisonCertificate states kernel reference)
    (observable : State → Q') (bound : Q')
    (bound_nonnegative : (0 : Q') ≤ bound)
    (observable_bound :
      ∀ target, target ∈ states →
        Q'.abs (observable target) ≤ bound)
    (reference_zero :
      ∀ source, source ∈ states →
        finiteObservableAction states reference observable source ≈ 0)
    (source : State) (hsource : source ∈ states) :
    Q'.abs
        (finiteObservableAction states kernel observable source) ≤
      certificate.epsilon * bound := by
  exact finiteObservableAction_centered_abs_le
    states kernel reference observable source bound certificate.epsilon
    bound_nonnegative observable_bound
    (reference_zero source hsource)
    (certificate.row_defect_le source hsource)

end FiniteRefreshComparisonCertificate

end YMGap.Continuum.FiniteRefreshSpectralComparison

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparison.finiteRowL1Defect_eqv_zero_of_pointwise
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparison.finiteObservableAction_centered_abs_le
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparison.FiniteRefreshComparisonCertificate.contractionMargin_pos
#print axioms
  YMGap.Continuum.FiniteRefreshSpectralComparison.FiniteRefreshComparisonCertificate.centeredAction_abs_le
