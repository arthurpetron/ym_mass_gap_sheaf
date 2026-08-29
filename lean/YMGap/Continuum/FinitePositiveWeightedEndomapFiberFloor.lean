/-
# A constructive positive floor for finite weighted endomap fibers

Let a finite carrier have strictly positive exact rational weights, and let a
deterministic endomap send each state to a terminal state.  For each displayed
target, compare its weight with the complete weight of its inverse fiber.  An
empty fiber has unit ratio; a nonempty fiber has the exact positive ratio

  target weight / inverse-fiber weight.

The capped minimum of these finitely many ratios is therefore strictly
positive, at most one, and fits every weighted inverse fiber into its target.
The rate is explicit data computed from the carrier, weights, and endomap.
It is not asserted to remain bounded below when any of those inputs vary.

Constructive contract: finite filters, exact positive rational division, and
finite positive minima only; no `Classical`, choice, `native_decide`, `sorry`,
new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
import YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
import YMGap.Continuum.FiniteDeterministicKernelPushforward

namespace YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.FiniteDependentKernelFirstSourcePositivity
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

/-! ## 1. Exact positive target-to-fiber ratios -/

def finitePositiveEndomapFiberItems
    {State : Type} [DecidableEq State]
    (states : List State) (code : State → State) (target : State) :
    List State :=
  states.filter fun state => decide (target = code state)

theorem finitePositiveEndomapFiberWeight_pos_of_ne_nil
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) (target : State)
    (hne : finitePositiveEndomapFiberItems states code target ≠ []) :
    (0 : Q') < fiberWeight states weight code target := by
  cases hfiber : finitePositiveEndomapFiberItems states code target with
  | nil => exact False.elim (hne hfiber)
  | cons first rest =>
      change (0 : Q') < listQSum weight
        (finitePositiveEndomapFiberItems states code target)
      rw [hfiber]
      exact listQSum_pos_of_mem weight
        (fun state => Q'.le_of_lt (weight_pos state))
        (first :: rest) List.mem_cons_self (weight_pos first)

/-- Exact target-capacity ratio, with unit value on an empty inverse fiber. -/
def finitePositiveEndomapFiberRatio
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) (target : State) : Q' :=
  if hempty : finitePositiveEndomapFiberItems states code target = [] then
    1
  else
    Q'.divPos (weight target) (fiberWeight states weight code target)
      (finitePositiveEndomapFiberWeight_pos_of_ne_nil
        states weight weight_pos code target hempty)

theorem finitePositiveEndomapFiberRatio_pos
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) (target : State) :
    (0 : Q') < finitePositiveEndomapFiberRatio
      states weight weight_pos code target := by
  unfold finitePositiveEndomapFiberRatio
  by_cases hempty : finitePositiveEndomapFiberItems states code target = []
  · rw [dif_pos hempty]
    decide
  · rw [dif_neg hempty]
    exact Q'.divPos_pos _ _ _ (weight_pos target)

/-! ## 2. One explicit common finite floor -/

/-- Capped positive minimum of the exact target-capacity ratios. -/
def finitePositiveEndomapFiberRate
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) : Q' :=
  listPositiveMinOne
    (finitePositiveEndomapFiberRatio states weight weight_pos code)
    states

theorem finitePositiveEndomapFiberRate_pos
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) :
    (0 : Q') < finitePositiveEndomapFiberRate
      states weight weight_pos code := by
  unfold finitePositiveEndomapFiberRate
  apply listPositiveMinOne_pos
  intro target _
  exact finitePositiveEndomapFiberRatio_pos
    states weight weight_pos code target

private theorem listPositiveMinOne_le_one_local
    {State : Type} (value : State → Q') : ∀ states : List State,
    listPositiveMinOne value states ≤ (1 : Q')
  | [] => Q'.le_refl' 1
  | _ :: rest =>
      Q'.le_trans' _ _ _ (Q'.min_le_right' _ _)
        (listPositiveMinOne_le_one_local value rest)

theorem finitePositiveEndomapFiberRate_le_one
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) :
    finitePositiveEndomapFiberRate states weight weight_pos code ≤
      (1 : Q') := by
  unfold finitePositiveEndomapFiberRate
  exact listPositiveMinOne_le_one_local _ states

/-- **Finite weighted-fiber floor.**  Every displayed target receives enough
capacity for the complete inverse fiber under the explicit common rate. -/
theorem finitePositiveEndomapFiberRate_mul_fiberWeight_le
    {State : Type} [DecidableEq State]
    (states : List State) (weight : State → Q')
    (weight_pos : ∀ state, (0 : Q') < weight state)
    (code : State → State) (target : State)
    (htarget : target ∈ states) :
    finitePositiveEndomapFiberRate states weight weight_pos code *
        fiberWeight states weight code target ≤
      weight target := by
  by_cases hempty : finitePositiveEndomapFiberItems
      states code target = []
  · have hfiberZero : fiberWeight states weight code target = 0 := by
      change listQSum weight
        (finitePositiveEndomapFiberItems states code target) = 0
      rw [hempty]
      rfl
    rw [hfiberZero]
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_zero_eqv
          (finitePositiveEndomapFiberRate
            states weight weight_pos code)))
      (Q'.le_of_lt (weight_pos target))
  · have hrate : finitePositiveEndomapFiberRate
        states weight weight_pos code ≤
      finitePositiveEndomapFiberRatio
        states weight weight_pos code target := by
      unfold finitePositiveEndomapFiberRate
      exact listPositiveMinOne_le_of_mem _ states target htarget
    have hfiberNonnegative : (0 : Q') ≤
        fiberWeight states weight code target := by
      unfold fiberWeight
      apply listQSum_nonnegative_on
      intro state _
      exact Q'.le_of_lt (weight_pos state)
    have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _
      hrate hfiberNonnegative
    exact Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv (by
        unfold finitePositiveEndomapFiberRatio
        rw [dif_neg hempty]
        exact Q'.divPos_mul_eqv
          (weight target) (fiberWeight states weight code target)
          (finitePositiveEndomapFiberWeight_pos_of_ne_nil
            states weight weight_pos code target hempty)))

#print axioms finitePositiveEndomapFiberWeight_pos_of_ne_nil
#print axioms finitePositiveEndomapFiberRatio_pos
#print axioms finitePositiveEndomapFiberRate_pos
#print axioms finitePositiveEndomapFiberRate_le_one
#print axioms finitePositiveEndomapFiberRate_mul_fiberWeight_le

end YMGap.Continuum.FinitePositiveWeightedEndomapFiberFloor
