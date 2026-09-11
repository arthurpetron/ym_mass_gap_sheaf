/-
# Weighted bounds for nested closed Boolean-tensor networks

A selected cutoff-one Haar channel contributes one inverse-Gram weight and
two endpoint factors at each physical link.  The graphical contraction bound
therefore controls the square of the selected network by the square of the
product of its local channel norms.  Since each local inverse-Gram weight
times its channel norm is exactly one, the weighted selected network has
absolute value at most one.

This file proves that cancellation abstractly and then folds it through a
nested family of local channel lists.  No Cartesian product of global channel
choices is constructed.

# Constructive discipline

There is no `Classical`, square root, assignment carrier, `native_decide`,
`sorry`/`admit`, or custom axiom.
-/

import YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan
import YMGap.Continuum.FactoredPositiveChannelTraceBound

namespace YMGap.Continuum.SymbolicFiniteBoolTensorWeightedContractionBound

open YMGap.Constructive
open YMGap.Continuum.OSReconstructionProgress
open YMGap.Continuum.SymbolicFiniteBoolTensorContractionPlan
open YMGap.Continuum.FactoredPositiveChannelTraceBound

local infix:50 " ≈ " => Q'.eqv

private theorem q_mul_congr {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right a a' b ha)
    (Q'.mul_eqv_congr_left a' b b' hb)

/-! ## 1. One weighted closed contraction -/

/-- Squaring a normalized weighted closed contraction removes every square
root: the squared weight multiplies the contraction-tree square estimate and
the exact relation `weight * localMass ≈ 1` closes the bound. -/
theorem weighted_closed_eval_square_le_one
    (plan : BoolTensorContractionPlan 0)
    (weight localMass : Q')
    (hleaf : plan.leafMass ≈ localMass * localMass)
    (hnormalized : weight * localMass ≈ 1) :
    (weight * (show Q' from plan.eval)) *
        (weight * (show Q' from plan.eval)) <= (1 : Q') := by
  let value : Q' := show Q' from plan.eval
  have hweightSquare : (0 : Q') <= weight * weight :=
    SumOfSquares.q_mul_self_nonneg weight
  have hscaled :
      (weight * weight) * (value * value) <=
        (weight * weight) * plan.leafMass :=
    Q'.mul_le_mul_of_nonneg_left
      (value * value) plan.leafMass (weight * weight)
      plan.closed_eval_square_le_leafMass hweightSquare
  have hleft :
      (weight * value) * (weight * value) ≈
        (weight * weight) * (value * value) :=
    mul4_rearrange weight value weight value
  have hnormalizedSquare :
      (weight * localMass) * (weight * localMass) ≈ (1 : Q') := by
    refine Q'.eqv_trans _ (1 * (weight * localMass)) _
      (Q'.mul_eqv_congr_right
        (weight * localMass) 1 (weight * localMass) hnormalized) ?_
    refine Q'.eqv_trans _ (1 * 1) _
      (Q'.mul_eqv_congr_left
        1 (weight * localMass) 1 hnormalized) ?_
    exact Q'.one_mul_eqv 1
  have hright :
      (weight * weight) * plan.leafMass ≈ (1 : Q') := by
    refine Q'.eqv_trans _
      ((weight * weight) * (localMass * localMass)) _
      (Q'.mul_eqv_congr_left
        (weight * weight) plan.leafMass
        (localMass * localMass) hleaf) ?_
    exact Q'.eqv_trans _ _ _
      (mul4_rearrange weight weight localMass localMass)
      hnormalizedSquare
  exact le_of_eqv_le hleft (le_of_le_eqv hscaled hright)

/-- A normalized weighted closed contraction lies in the unit absolute-value
interval. -/
theorem weighted_closed_eval_abs_le_one
    (plan : BoolTensorContractionPlan 0)
    (weight localMass : Q')
    (hleaf : plan.leafMass ≈ localMass * localMass)
    (hnormalized : weight * localMass ≈ 1) :
    Q'.abs (weight * (show Q' from plan.eval)) <= (1 : Q') :=
  BoolTensorContractionPlan.abs_le_one_of_square_le_one
    (weight * (show Q' from plan.eval))
    (weighted_closed_eval_square_le_one
      plan weight localMass hleaf hnormalized)

/-! ## 2. Linkwise normalization along one selected channel word -/

/-- A structural product of pointwise unit-equivalent factors remains
unit-equivalent. -/
theorem listQProduct_eqv_one {A : Type} (factor : A -> Q')
    (hfactor : forall value, factor value ≈ 1) :
    forall selected : List A, listQProduct factor selected ≈ 1
  | [] => Q'.eqv_refl 1
  | value :: selected => by
      refine Q'.eqv_trans _ (1 * 1) _
        (q_mul_congr (hfactor value)
          (listQProduct_eqv_one factor hfactor selected)) ?_
      exact Q'.one_mul_eqv 1

/-- Exact linkwise cancellation of a product of inverse-Gram weights against
the product of local channel norms. -/
theorem selectedWeight_mul_selectedMass_eqv_one {A : Type}
    (weight localMass : A -> Q')
    (hnormalized : forall value, weight value * localMass value ≈ 1) :
    forall selected : List A,
      listQProduct weight selected * listQProduct localMass selected ≈ 1
  | selected =>
      Q'.eqv_trans _ _ _
        (listQProduct_mul weight localMass selected)
        (listQProduct_eqv_one
          (fun value => weight value * localMass value)
          hnormalized selected)

/-! ## 3. Nested channel families -/

/-- Structural number of global channel selections, represented without a
Cartesian product list. -/
def nestedChoiceMass {A : Type} (choiceLists : List (List A)) : Q' :=
  nestedListQSum choiceLists (fun _ => 1)

/-- **Nested weighted graphical bound.**

For every structurally selected local-channel word, an explicit closed
contraction plan is allowed.  If its leaf mass is the square of the product
of local channel norms, and each local weight normalizes its local norm, then
the absolute value of the nested weighted network sum is bounded by the
structural number of channel selections. -/
theorem abs_nestedWeightedClosedEval_le_choiceMass {A : Type}
    (choiceLists : List (List A))
    (plan : List A -> BoolTensorContractionPlan 0)
    (weight localMass : A -> Q')
    (hleaf : forall selected,
      (plan selected).leafMass ≈
        listQProduct localMass selected *
          listQProduct localMass selected)
    (hnormalized : forall value,
      weight value * localMass value ≈ 1) :
    Q'.abs
        (nestedListQSum choiceLists (fun selected =>
          listQProduct weight selected *
            (show Q' from (plan selected).eval))) <=
      nestedChoiceMass choiceLists := by
  unfold nestedChoiceMass
  exact abs_nestedListQSum_le choiceLists _ _ (fun selected =>
    weighted_closed_eval_abs_le_one
      (plan selected)
      (listQProduct weight selected)
      (listQProduct localMass selected)
      (hleaf selected)
      (selectedWeight_mul_selectedMass_eqv_one
        weight localMass hnormalized selected))

/-! ## Axiom audit -/

#print axioms weighted_closed_eval_square_le_one
#print axioms weighted_closed_eval_abs_le_one
#print axioms listQProduct_eqv_one
#print axioms selectedWeight_mul_selectedMass_eqv_one
#print axioms abs_nestedWeightedClosedEval_le_choiceMass

end YMGap.Continuum.SymbolicFiniteBoolTensorWeightedContractionBound
