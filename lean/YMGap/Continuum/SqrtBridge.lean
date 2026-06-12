/-
The √-bridge: `m_0 = √σ̂_∞` as a genuine constructive real (Milestone F.5,
`docs/uniform-parametric-bound-plan.md` Part II.4).

# Why this module exists

The SU(2) mass bound was carried as a `Q'`-rational threshold `m_0² ≤ σ̂_∞`
(decidable), and the dimensional identification `m ≥ √σ̂_∞` was paper-only.
`Constructive/Sqrt.lean` now provides a genuine constructive square root
`CReal.sqrtFrom` (Heron iteration, explicit Type-level modulus, axiom-clean),
proving it is positive for positive input and satisfies `(√a)² ≃ a`.

This module plugs that into the σ̂_∞ application: it defines the mass

    m_0 := √σ̂_∞    (a `CReal`),

with witnessed positivity inherited from the proved `σ̂_∞ > 0`, and the proved
square identity `m_0² ≃ σ̂_∞` (`CReal.Equiv`).  The √-content is now a Lean
theorem, not an assumption; only the dimensional (mass-units) interpretation
remains the paper's province.

For the UV-direction pilot, `σ̂_∞ = ofQ' 1` (the σ̂_N trajectory is the constant
`σ̂_0 = 1`), so `m_0 = √1` and the conservative O(1) area-law constant is `1`
explicitly.  The construction is fully general in the square-root value: any
positive rational `a` with a positive rational lower-bound witness `L` (`L² ≤ a`)
gives `√a` via `CReal.sqrtFrom`.

# Axiom-gate (AGENTS.md Rule 1)

Every theorem reports `[propext, Quot.sound]` only (the `Quot.sound` from
`omega`/`Nat` in the underlying Heron analysis).  No `Classical.*`, no `sorryAx`.
-/

import YMGap.Constructive.Sqrt
import YMGap.Constructive.Reals

namespace YMGap.Continuum.SqrtBridge

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.RG.SigmaHatPilotUV

/-! ## The rational value of σ̂_∞ and its lower-bound witness

`σ̂_∞ = ofQ' 1` for the UV pilot.  We expose the rational value `sigmaHatVal = 1`
and its lower-bound witness `L = 1` (`1·1 ≤ 1`), the inputs `sqrtFrom` consumes. -/

/-- The rational value of σ̂_∞ for the UV pilot: `1`. -/
def sigmaHatVal : Q' := sigma_hat_0_pilot_uv

theorem sigmaHatVal_pos : (0 : Q') < sigmaHatVal := by decide

/-- A positive rational lower-bound witness: `L = 1`, with `L² ≤ σ̂_∞`. -/
def sqrtL : Q' := 1

theorem sqrtL_pos : (0 : Q') < sqrtL := by decide

theorem sqrtL_sq_le : sqrtL * sqrtL ≤ sigmaHatVal := by decide

/-- `sigma_hat_inf_creal` is definitionally `ofQ' sigmaHatVal`. -/
theorem sigma_hat_inf_creal_eq_ofQ' :
    sigma_hat_inf_creal = CReal.ofQ' sigmaHatVal := rfl

/-! ## The mass `m_0 = √σ̂_∞` -/

/-- **The mass `m_0 = √σ̂_∞`** as a genuine constructive real. -/
def m_0 : CReal := CReal.sqrtFrom sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **`m_0 > 0`** — the dimensional positivity of the mass, witnessed by the
rational lower bound `L`, ultimately from `σ̂_∞ > 0`. -/
theorem m_0_isPositive : CReal.IsPositive m_0 :=
  CReal.sqrtFrom_isPositive sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **`m_0² ≃ σ̂_∞`** — the defining square identity of the √-bridge:
the square of the mass is `CReal.Equiv` to σ̂_∞. -/
theorem m_0_sq_equiv_sigma_hat :
    CReal.Equiv (CReal.mul m_0 m_0) sigma_hat_inf_creal := by
  -- (√a)² ≃ ofQ' a = σ̂_∞
  rw [sigma_hat_inf_creal_eq_ofQ']
  exact CReal.sqrtFrom_sq_equiv sigmaHatVal sqrtL sigmaHatVal_pos sqrtL_pos sqrtL_sq_le

/-- **The √-bridge, packaged.**  There is a constructive real `m_0` that is
strictly positive and whose square is `σ̂_∞`: the genuine Lean form of
`m_0 = √σ̂_∞`, `m_0 > 0`, `m_0² ≃ σ̂_∞`. -/
def sqrt_bridge :
    Σ' m : CReal, CReal.IsPositive m ∧ CReal.Equiv (CReal.mul m m) sigma_hat_inf_creal :=
  ⟨m_0, m_0_isPositive, m_0_sq_equiv_sigma_hat⟩

end YMGap.Continuum.SqrtBridge

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.SqrtBridge.sigmaHatVal_pos
#print axioms YMGap.Continuum.SqrtBridge.sqrtL_sq_le
#print axioms YMGap.Continuum.SqrtBridge.m_0
#print axioms YMGap.Continuum.SqrtBridge.m_0_isPositive
#print axioms YMGap.Continuum.SqrtBridge.m_0_sq_equiv_sigma_hat
#print axioms YMGap.Continuum.SqrtBridge.sqrt_bridge
