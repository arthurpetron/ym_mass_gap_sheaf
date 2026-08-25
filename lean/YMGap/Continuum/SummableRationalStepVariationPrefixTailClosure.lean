/-
# Computed prefix plus analytic tail closure for rational step variation

A summable rational step variation supplies a tail modulus, but a persistence
consumer may need one budget whose stored tail rate is literally zero.  That
extra datum is not an independent analytic hypothesis.  Given any positive
tail allowance, ask the original modulus for its cutoff, compute the exact
finite variation prefix up to that cutoff, and add the two quantities.

This module proves that the resulting rational controls every finite variation
window and installs a budget-normalized tail modulus.  Consequently any
`SummableRationalStepVariation` can be re-packaged so that its computed total
budget has tail rate zero, without altering its stream, variation, or local
step bounds.

No physical variation or initial-slack estimate is supplied.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Constructive.CornerBound
import YMGap.Constructive.Sqrt
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.SummableCRealStepVariation
open YMGap.Continuum.SummableRationalStepVariation

private theorem finSum_nonnegative_local
    (stream : Nat -> Q')
    (hstream : forall scale, (0 : Q') <= stream scale) :
    forall length, (0 : Q') <= finSum stream length
  | 0 => Q'.le_refl' 0
  | length + 1 =>
      Q'.zero_le_add _ _
        (finSum_nonnegative_local stream hstream length)
        (hstream length)

private theorem right_le_sum
    (left right : Q') (hleft : (0 : Q') <= left) :
    right <= left + right := by
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg right left hleft)
    (Q'.le_of_eqv (Q'.add_comm_eqv right left))

/-! ## 1. Compute a total budget from one tail allowance -/

def prefixTailStart
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q') : Nat :=
  data.tailControl.tailRate tailAllowance

def prefixTailPrefix
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q') : Q' :=
  finSum data.variation (prefixTailStart data tailAllowance)

/-- The positive allowance is placed first, so budget positivity follows
constructively even when the computed finite prefix is zero. -/
def prefixTailTotalBudget
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q') : Q' :=
  tailAllowance + prefixTailPrefix data tailAllowance

theorem prefixTailPrefix_nonnegative
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q') :
    (0 : Q') <= prefixTailPrefix data tailAllowance := by
  unfold prefixTailPrefix
  exact finSum_nonnegative_local _ data.variation_nonnegative _

theorem prefixTailTotalBudget_pos
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    (0 : Q') < prefixTailTotalBudget data tailAllowance := by
  unfold prefixTailTotalBudget
  exact Q'.pos_add_nonneg tailAllowance_pos
    (prefixTailPrefix_nonnegative data tailAllowance)

/-! ## 2. The computed budget controls all finite windows -/

theorem variationPartialSum_le_totalBudget
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (length : Nat) :
    finSum data.variation length <=
      prefixTailTotalBudget data tailAllowance := by
  let tailStart := prefixTailStart data tailAllowance
  let prefixSum := prefixTailPrefix data tailAllowance
  have hprefixNonnegative : (0 : Q') <= prefixSum := by
    exact prefixTailPrefix_nonnegative data tailAllowance
  rcases Nat.le_total length tailStart with hbefore | hafter
  · have hprefix : finSum data.variation length <= prefixSum := by
      unfold prefixSum prefixTailPrefix
      exact finSum_monotone_of_nonneg
        data.variation data.variation_nonnegative
        length tailStart hbefore
    have hgrow : prefixSum <= prefixSum + tailAllowance :=
      Q'.add_le_self_of_nonneg prefixSum tailAllowance
        (Q'.le_of_lt tailAllowance_pos)
    exact Q'.le_trans' _ _ _ hprefix
      (Q'.le_trans' _ _ _ hgrow
        (Q'.le_of_eqv (Q'.add_comm_eqv prefixSum tailAllowance)))
  · obtain ⟨tailLength, hlength⟩ := Nat.exists_eq_add_of_le hafter
    rw [hlength]
    have htail :
        finSum
            (fun offset => data.variation (tailStart + offset))
            tailLength <= tailAllowance := by
      exact data.tailControl.tailBound tailAllowance tailAllowance_pos
        tailStart (Nat.le_refl tailStart) tailLength
    have hsplit :=
      YMGap.Constructive.finSum_split
        data.variation tailStart tailLength
    have hsum :
        finSum data.variation (tailStart + tailLength) <=
          prefixSum + tailAllowance := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsplit)
        (Q'.add_le_add_left prefixSum _ _ htail)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.add_comm_eqv prefixSum tailAllowance))

theorem variationWindow_le_totalBudget
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (start length : Nat) :
    finSum (fun offset => data.variation (start + offset)) length <=
      prefixTailTotalBudget data tailAllowance := by
  have hprefixNonnegative :
      (0 : Q') <= finSum data.variation start :=
    finSum_nonnegative_local _ data.variation_nonnegative start
  have hsplit :=
    YMGap.Constructive.finSum_split data.variation start length
  have hwindow :
      finSum (fun offset => data.variation (start + offset)) length <=
        finSum data.variation (start + length) := by
    exact Q'.le_trans' _ _ _
      (right_le_sum _ _ hprefixNonnegative)
      (Q'.ge_of_eqv hsplit)
  exact Q'.le_trans' _ _ _ hwindow
    (variationPartialSum_le_totalBudget
      data tailAllowance tailAllowance_pos (start + length))

/-! ## 3. Normalize the tail modulus at the computed budget -/

def budgetedTailControl
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    AntitoneTailControl data.variation where
  tailRate := fun epsilon =>
    if prefixTailTotalBudget data tailAllowance <= epsilon
    then 0
    else data.tailControl.tailRate epsilon
  tailRate_antitone := by
    intro epsilon delta delta_pos delta_le_epsilon
    by_cases hepsilon :
        prefixTailTotalBudget data tailAllowance <= epsilon
    · rw [if_pos hepsilon]
      exact Nat.zero_le _
    · have hdelta :
          ¬ prefixTailTotalBudget data tailAllowance <= delta := by
        intro hbudget
        exact hepsilon (Q'.le_trans' _ _ _ hbudget delta_le_epsilon)
      rw [if_neg hepsilon, if_neg hdelta]
      exact data.tailControl.tailRate_antitone
        epsilon delta delta_pos delta_le_epsilon
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    by_cases hbudget :
        prefixTailTotalBudget data tailAllowance <= epsilon
    · exact Q'.le_trans' _ _ _
        (variationWindow_le_totalBudget
          data tailAllowance tailAllowance_pos start length)
        hbudget
    · have htailStart : data.tailControl.tailRate epsilon <= start := by
        simpa only [hbudget, if_false] using start_bound
      exact data.tailControl.tailBound epsilon epsilon_pos
        start htailStart length

theorem budgetedTailControl_rate_totalBudget
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    (budgetedTailControl data tailAllowance tailAllowance_pos).tailRate
        (prefixTailTotalBudget data tailAllowance) = 0 := by
  unfold budgetedTailControl
  change
    (if prefixTailTotalBudget data tailAllowance <=
        prefixTailTotalBudget data tailAllowance
      then 0
      else data.tailControl.tailRate
        (prefixTailTotalBudget data tailAllowance)) = 0
  rw [if_pos (Q'.le_refl' (prefixTailTotalBudget data tailAllowance))]

/-- Re-package the same stream, variation, and local bounds with the computed
budget-normalized tail modulus. -/
def budgetedVariation
    {stream : Nat -> Q'}
    (data : SummableRationalStepVariation stream)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    SummableRationalStepVariation stream where
  variation := data.variation
  variation_nonnegative := data.variation_nonnegative
  tailControl := budgetedTailControl data tailAllowance tailAllowance_pos
  stepBound := data.stepBound

end YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.prefixTailStart
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.prefixTailTotalBudget
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.prefixTailTotalBudget_pos
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.variationPartialSum_le_totalBudget
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.variationWindow_le_totalBudget
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.budgetedTailControl
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.budgetedTailControl_rate_totalBudget
#print axioms YMGap.Continuum.SummableRationalStepVariationPrefixTailClosure.budgetedVariation
