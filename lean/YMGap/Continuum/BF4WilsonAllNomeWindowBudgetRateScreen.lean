/-
# The original window budget is capped by the SAME carrier's fixed-nome rate

For a vacuum-orthogonal completed vector, the existing iterated norm gap gives
`R(4u) <= mixRate^(2u) R(2u)`. Hence any macroscopic ratio, and in particular
the window budget hypothesis of `aggregate_window_macro_ratio` and the
ORIGINAL eventual budget of `original_window_budget_macro_ratio`
(`BF4WilsonAllNomeWindowSignedCost.lean:245`), forces
`kappa*R(2u) <= mixRate^(2u)*R(2u)`.

Scope: a necessary screen only. `mixRate = 1-(headFloor/prefixCap)^#faces`
is volume-exponentially close to one, so this screen neither refutes nor
supports a useful budget; a useful spectral argument would have to be
width-uniform. No budget, survival floor or scaling family is supplied.
-/

import YMGap.Continuum.BF4WilsonAllNomeWindowSignedCost
import YMGap.Continuum.BF4WilsonAllNomeCompletedGap

namespace YMGap.Continuum.BF4WilsonAllNomeWindowBudgetRateScreen

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4WilsonAllNomeCompletedInner
open YMGap.Continuum.BF4WilsonAllNomeCompletedTime
open YMGap.Continuum.BF4WilsonAllNomeCompletedGap
  (completed_iterated_norm_gap completedInner_even_diagonal)
open YMGap.Continuum.BF4ExactSlabFixedSpatialDenseCenteredGap (twoStepRate)
open YMGap.Continuum.BF4WilsonAllNomeWindowSignedCost
  (windowSignedCost aggregate_window_macro_ratio original_window_budget_macro_ratio
   originalWindowCost)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicUnitExcitation dyadicUnitResponse_pin)
open YMGap.Continuum.BF4WilsonAllNomeDyadicOriginalRayleighLimit (originalOwnBlockVariance)
open YMGap.Continuum.BF4DyadicWilsonSquare (side)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (width : Nat)

local notation "V" => Completion hw0 hw1 width
local notation "B" => completedInner hw0 hw1
local notation "T" => completedTime hw0 hw1
local notation "U" => unitState hw0 hw1 width

/-- Any macroscopic ratio on a vacuum-orthogonal vector is capped by the
SAME carrier's fixed-nome rate: `kappa R(2u) <= mixRate^(2u) R(2u)`
(`twoStepRate = mixRate^2`). -/
theorem macro_ratio_rate_screen (x : V) (hx : B U x = RCzero) (u : Nat) (kappa : Q')
    (hratio : RCle (RCscale kappa (B x (T (2*u) x))) (B x (T (4*u) x))) :
    RCle (RCscale kappa (B x (T (2*u) x)))
      (RCscale ((twoStepRate hw0 hw1 width)^u) (B x (T (2*u) x))) := by
  have hy : B (T u x) U = RCzero := by
    rw [completedInner_symm]
    exact completedTime_preserves_vacuumComplement hw0 hw1 u x hx
  have h2 := completed_iterated_norm_gap hw0 hw1 width u (T u x) hy
  have e4 : B x (T (4*u) x) = B (T u (T u x)) (T u (T u x)) := by
    rw [← completedTime_add, show 4*u = 2*(u+u) by omega, completedInner_even_diagonal]
  have e2 : B x (T (2*u) x) = B (T u x) (T u x) :=
    completedInner_even_diagonal hw0 hw1 width u x
  rw [e4, e2] at hratio
  rw [e2]
  exact RCle_trans hratio h2

/-- The window-budget hypothesis of `aggregate_window_macro_ratio` is capped
in the same way. -/
theorem window_budget_rate_screen (x : V) (hx : B U x = RCzero) (u : Nat) (kappa : Q')
    (hbudget : RCle (RCscale 2 (windowSignedCost hw0 hw1 x u u))
      (RCscale (1-kappa) (B x (T (2*u) x)))) :
    RCle (RCscale kappa (B x (T (2*u) x)))
      (RCscale ((twoStepRate hw0 hw1 width)^u) (B x (T (2*u) x))) :=
  macro_ratio_rate_screen hw0 hw1 width x hx u kappa
    (aggregate_window_macro_ratio hw0 hw1 x u kappa hbudget)

/-- The ORIGINAL eventual budget (`BF4WilsonAllNomeWindowSignedCost.lean:245`)
for the literal dyadic unit excitation is capped by the same carrier rate. -/
theorem original_window_budget_rate_screen (scale : Nat) (hwidth : side scale < width)
    (u : Nat) (kappa : Q') (onset : Nat)
    (hbudget : ∀ stage, onset ≤ stage →
      2*originalWindowCost hw0 hw1 scale width hwidth stage u u ≤
        (1-kappa)*originalOwnBlockVariance hw0 hw1 scale width hwidth stage u) :
    let x := (dyadicUnitExcitation hw0 hw1 scale width hwidth).val
    RCle (RCscale kappa (B x (T (2*u) x)))
      (RCscale ((twoStepRate hw0 hw1 width)^u) (B x (T (2*u) x))) := by
  intro x
  have h := original_window_budget_macro_ratio hw0 hw1 scale width hwidth u kappa onset hbudget
  have hrc : RCle (RCscale kappa (B x (T (2*u) x))) (B x (T (4*u) x)) := by
    rw [dyadicUnitResponse_pin, dyadicUnitResponse_pin, RCscale_mk]
    exact h
  exact macro_ratio_rate_screen hw0 hw1 width x
    (dyadicUnitExcitation hw0 hw1 scale width hwidth).property u kappa hrc

#print axioms macro_ratio_rate_screen
#print axioms window_budget_rate_screen
#print axioms original_window_budget_rate_screen

end YMGap.Continuum.BF4WilsonAllNomeWindowBudgetRateScreen
