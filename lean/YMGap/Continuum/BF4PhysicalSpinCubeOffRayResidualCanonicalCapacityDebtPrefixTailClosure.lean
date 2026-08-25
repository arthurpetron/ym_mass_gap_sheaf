/-
# Computed prefix plus analytic tail closure for canonical BF4 capacity debt

One antitone tail control proves summability only beyond a computed cutoff.
The persistence compiler additionally wants a budget whose stored tail rate is
literally zero, so that the budget controls variation from cutoff zero.  That
literal requirement should not be an independent analytic hypothesis.

For any positive tail allowance, this module asks the total-deficit tail
control for its cutoff, computes the exact finite prefix through that cutoff,
and defines the total budget as

  tail allowance + exact finite prefix.

Every partial sum is bounded by this budget.  A budget-normalized tail control
then reports rate zero whenever the requested tolerance covers the computed
total budget, while retaining the original analytic modulus for smaller
tolerances.  Hence one total-tail witness and one final scalar slack check
construct the existing correlated persistence and completed fixed-anchor
family.

No total-tail witness or slack inequality is supplied.  The fixed
strong-coupling anchor is not the physical AF/grouped-BF4 trajectory, and no
thermodynamic, continuum, or Clay conclusion is asserted.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, or noncomputable declaration
is used.
-/

import YMGap.Constructive.CornerBound
import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualAdaptiveSupportDebtVariationFactor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtCompiler
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtTotalDeficitCompiler
open YMGap.Continuum.SummableCRealStepVariation

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

/-! ## 1. The tail modulus selects a cutoff; the prefix is executable -/

def anchorCanonicalCapacityDebtTotalDeficitTailStart
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q') : Nat :=
  data.tailControl.tailRate tailAllowance

def anchorCanonicalCapacityDebtTotalDeficitPrefix
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q') : Q' :=
  finSum anchorCanonicalCapacityDebtTotalDeficit
    (anchorCanonicalCapacityDebtTotalDeficitTailStart data tailAllowance)

/-- The order puts the strictly positive allowance first, making positivity
constructive without demanding a positive finite prefix. -/
def anchorCanonicalCapacityDebtTotalBudget
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q') : Q' :=
  tailAllowance +
    anchorCanonicalCapacityDebtTotalDeficitPrefix data tailAllowance

theorem anchorCanonicalCapacityDebtTotalDeficitPrefix_nonnegative
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q') :
    (0 : Q') <=
      anchorCanonicalCapacityDebtTotalDeficitPrefix data tailAllowance := by
  unfold anchorCanonicalCapacityDebtTotalDeficitPrefix
  exact finSum_nonnegative_local _
    anchorCanonicalCapacityDebtTotalDeficit_nonnegative _

theorem anchorCanonicalCapacityDebtTotalBudget_pos
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    (0 : Q') <
      anchorCanonicalCapacityDebtTotalBudget data tailAllowance := by
  unfold anchorCanonicalCapacityDebtTotalBudget
  exact Q'.pos_add_nonneg tailAllowance_pos
    (anchorCanonicalCapacityDebtTotalDeficitPrefix_nonnegative
      data tailAllowance)

/-! ## 2. The computed budget covers every finite variation prefix -/

theorem anchorCanonicalCapacityDebtTotalDeficitPartialSum_le_budget
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (length : Nat) :
    finSum anchorCanonicalCapacityDebtTotalDeficit length <=
      anchorCanonicalCapacityDebtTotalBudget data tailAllowance := by
  let tailStart :=
    anchorCanonicalCapacityDebtTotalDeficitTailStart data tailAllowance
  let prefixSum :=
    anchorCanonicalCapacityDebtTotalDeficitPrefix data tailAllowance
  have hprefixNonnegative : (0 : Q') <= prefixSum := by
    exact anchorCanonicalCapacityDebtTotalDeficitPrefix_nonnegative
      data tailAllowance
  rcases Nat.le_total length tailStart with hbefore | hafter
  · have hprefix :
        finSum anchorCanonicalCapacityDebtTotalDeficit length <= prefixSum := by
      unfold prefixSum anchorCanonicalCapacityDebtTotalDeficitPrefix
      exact finSum_monotone_of_nonneg
        anchorCanonicalCapacityDebtTotalDeficit
        anchorCanonicalCapacityDebtTotalDeficit_nonnegative
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
            (fun offset =>
              anchorCanonicalCapacityDebtTotalDeficit
                (tailStart + offset)) tailLength <= tailAllowance := by
      exact data.tailControl.tailBound tailAllowance tailAllowance_pos
        tailStart (Nat.le_refl tailStart) tailLength
    have hsplit :=
      YMGap.Constructive.finSum_split
        anchorCanonicalCapacityDebtTotalDeficit tailStart tailLength
    have hsum :
        finSum anchorCanonicalCapacityDebtTotalDeficit
            (tailStart + tailLength) <=
          prefixSum + tailAllowance := by
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv hsplit)
        (Q'.add_le_add_left prefixSum _ _ htail)
    exact Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.add_comm_eqv prefixSum tailAllowance))

/-- Every shifted finite window is also covered by the same total budget. -/
theorem anchorCanonicalCapacityDebtTotalDeficitWindow_le_budget
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (start length : Nat) :
    finSum
        (fun offset =>
          anchorCanonicalCapacityDebtTotalDeficit (start + offset)) length <=
      anchorCanonicalCapacityDebtTotalBudget data tailAllowance := by
  have hprefixNonnegative : (0 : Q') <=
      finSum anchorCanonicalCapacityDebtTotalDeficit start :=
    finSum_nonnegative_local _
      anchorCanonicalCapacityDebtTotalDeficit_nonnegative start
  have hsplit :=
    YMGap.Constructive.finSum_split
      anchorCanonicalCapacityDebtTotalDeficit start length
  have hwindow :
      finSum
          (fun offset =>
            anchorCanonicalCapacityDebtTotalDeficit (start + offset)) length <=
        finSum anchorCanonicalCapacityDebtTotalDeficit (start + length) := by
    exact Q'.le_trans' _ _ _
      (right_le_sum _ _ hprefixNonnegative)
      (Q'.ge_of_eqv hsplit)
  exact Q'.le_trans' _ _ _ hwindow
    (anchorCanonicalCapacityDebtTotalDeficitPartialSum_le_budget
      data tailAllowance tailAllowance_pos (start + length))

/-! ## 3. Normalize the modulus so the computed budget starts at zero -/

def anchorCanonicalCapacityDebtBudgetedTailControl
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    AntitoneTailControl anchorCanonicalCapacityDebtTotalDeficit where
  tailRate := fun epsilon =>
    if anchorCanonicalCapacityDebtTotalBudget data tailAllowance <= epsilon
    then 0
    else data.tailControl.tailRate epsilon
  tailRate_antitone := by
    intro epsilon delta delta_pos delta_le_epsilon
    by_cases hepsilon :
        anchorCanonicalCapacityDebtTotalBudget data tailAllowance <= epsilon
    · rw [if_pos hepsilon]
      exact Nat.zero_le _
    · have hdelta :
          ¬ anchorCanonicalCapacityDebtTotalBudget data tailAllowance <=
            delta := by
        intro hbudget
        exact hepsilon (Q'.le_trans' _ _ _ hbudget delta_le_epsilon)
      rw [if_neg hepsilon, if_neg hdelta]
      exact data.tailControl.tailRate_antitone
        epsilon delta delta_pos delta_le_epsilon
  tailBound := by
    intro epsilon epsilon_pos start start_bound length
    by_cases hbudget :
        anchorCanonicalCapacityDebtTotalBudget data tailAllowance <= epsilon
    · exact Q'.le_trans' _ _ _
        (anchorCanonicalCapacityDebtTotalDeficitWindow_le_budget
          data tailAllowance tailAllowance_pos start length)
        hbudget
    · have htailStart : data.tailControl.tailRate epsilon <= start := by
        simpa only [hbudget, if_false] using start_bound
      exact data.tailControl.tailBound epsilon epsilon_pos
        start htailStart length

theorem anchorCanonicalCapacityDebtBudgetedTailControl_rate_budget
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    (anchorCanonicalCapacityDebtBudgetedTailControl
        data tailAllowance tailAllowance_pos).tailRate
          (anchorCanonicalCapacityDebtTotalBudget data tailAllowance) = 0 := by
  unfold anchorCanonicalCapacityDebtBudgetedTailControl
  change
    (if anchorCanonicalCapacityDebtTotalBudget data tailAllowance <=
        anchorCanonicalCapacityDebtTotalBudget data tailAllowance
      then 0
      else data.tailControl.tailRate
        (anchorCanonicalCapacityDebtTotalBudget data tailAllowance)) = 0
  rw [if_pos (Q'.le_refl'
    (anchorCanonicalCapacityDebtTotalBudget data tailAllowance))]

/-! ## 4. Prefix computation removes the separate budget-rate premise -/

def anchorCanonicalCapacityDebtBudgetedEnvelope
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance) :
    AnchorCanonicalCapacityDebtEnvelope where
  variation := anchorCanonicalCapacityDebtTotalDeficit
  variation_nonnegative :=
    anchorCanonicalCapacityDebtTotalDeficit_nonnegative
  tailControl :=
    anchorCanonicalCapacityDebtBudgetedTailControl
      data tailAllowance tailAllowance_pos
  current_le_next := data.toEnvelope.current_le_next
  next_le_current := data.toEnvelope.next_le_current

def anchorCanonicalCapacityDebtPersistenceOfPrefixTail
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget data tailAllowance <=
          (1 : Q')) :
    AnchorCanonicalCapacityDebtPersistence where
  envelope := anchorCanonicalCapacityDebtBudgetedEnvelope
    data tailAllowance tailAllowance_pos
  budget := anchorCanonicalCapacityDebtTotalBudget data tailAllowance
  budget_pos := anchorCanonicalCapacityDebtTotalBudget_pos
    data tailAllowance tailAllowance_pos
  budget_from_zero := by
    change
      (anchorCanonicalCapacityDebtBudgetedTailControl
          data tailAllowance tailAllowance_pos).tailRate
        (anchorCanonicalCapacityDebtTotalBudget data tailAllowance) = 0
    exact anchorCanonicalCapacityDebtBudgetedTailControl_rate_budget
      data tailAllowance tailAllowance_pos
  initial_closure := initial_closure

def anchorGeometricCompletedFamilyOfPrefixTail
    (data : AnchorCanonicalCapacityDebtTotalDeficitTail)
    (tailAllowance : Q')
    (tailAllowance_pos : (0 : Q') < tailAllowance)
    (initial_closure :
      anchorRoutedCapacityDebtMaximum
          anchorCanonicalPositiveRoutingSequence 0 +
        anchorCanonicalCapacityDebtTotalBudget data tailAllowance <=
          (1 : Q')) :
    BF4PhysicalDynamicVacuumSectorCompletedFamily.DynamicVacuumSectorCompletedFamily
      0 :=
  (anchorCanonicalCapacityDebtPersistenceOfPrefixTail
    data tailAllowance tailAllowance_pos initial_closure).toAnchorGeometricCompletedFamily

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalDeficitTailStart
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalDeficitPrefix
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalBudget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalBudget_pos
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalDeficitPartialSum_le_budget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtTotalDeficitWindow_le_budget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtBudgetedTailControl
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtBudgetedTailControl_rate_budget
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorCanonicalCapacityDebtPersistenceOfPrefixTail
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCanonicalCapacityDebtPrefixTailClosure.anchorGeometricCompletedFamilyOfPrefixTail
