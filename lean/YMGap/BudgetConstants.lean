/-
# Budget constants — the SINGLE SOURCE OF TRUTH for the SU(2) σ̂-budget chain

The pilot operating-point constants — the physical mass-gap margin `m₀`, the
renormalized string-tension lower bound `σ̂`, and the per-step budget defect
`η_max` — are threaded through the budget chain (`ModuliAlgebra`,
`RG.SigmaHatPilot`, `Codynamic`, `RepTheory.RepData`, `MassGap.*`,
`BufferShell`).  Historically each was duplicated as a `Q'.mkPos …` literal
across those files, so a change to any one required a matching edit everywhere
(and through `decide` proofs).

These are PILOT values.  When the real 4D Balaban defect scaling lands (the live
target per `CLAUDE.md`), they change.  This module names them ONCE so that
re-derivation is a **one-file change**: edit the `def`s here — every consumer
re-derives, and the downstream `decide`/`by decide` proofs re-check because they
unfold these `def`s to the underlying concrete `Q'`.

No analytic content lives here; these are just the named rational literals plus a
`BudgetConstants` bundle that a future scaling can re-instantiate.
-/
import YMGap.Constructive.Rationals

namespace YMGap.BudgetConstants

open YMGap.Constructive

/-- Physical mass-gap margin `m₀` at the SU(2) pilot operating point: `999/1000`.
Threaded as `m_0` / `m_inf` / `m_0_canonical` / `m_0_wilson`. -/
def bcMargin : Q' := Q'.mkPos 999 1000 (by decide)

/-- Renormalized string-tension lower bound `σ̂` at the pilot: `9991/10000`
(post-`c_λ`-Casimir-gap upgrade).  Threaded as `sigma_hat_k` / `sigma_phys` /
`su2_gap` / `sigma_hat_inf_lower_canonical`. -/
def bcSigmaHat : Q' := Q'.mkPos 9991 10000 (by decide)

/-- Per-step budget defect `η_max` at the canonical pilot (`g₀ = 0.30`,
post-`c_λ`-upgrade): `3/10000 = 3·10⁻⁴`.  Threaded as `eta_max_pilot` /
`eta_total_pilot_wilson` / `numerical_upper`. -/
def bcEtaMaxCanonical : Q' := Q'.mkPos 3 10000 (by decide)

/-- Per-step budget defect `η_max` for the all-simple-types worst case:
`13/1000000 = 13·10⁻⁶`. -/
def bcEtaMaxSimple : Q' := Q'.mkPos 13 1000000 (by decide)

/-- **`BudgetConstants`** — the pilot operating-point bundle.  A future Balaban
scaling supplies a new instance; every consumer that reads its fields re-derives.
-/
structure BudgetConstants where
  /-- Physical mass-gap margin `m₀`. -/
  margin : Q'
  /-- Renormalized string-tension lower bound `σ̂`. -/
  sigmaHat : Q'
  /-- Per-step budget defect `η_max`. -/
  etaMax : Q'

/-- The current SU(2) pilot instance (canonical `η_max`). -/
def pilotBudget : BudgetConstants :=
  { margin := bcMargin, sigmaHat := bcSigmaHat, etaMax := bcEtaMaxCanonical }

/-- The all-simple-types pilot instance (worst-case `η_max`). -/
def simplePilotBudget : BudgetConstants :=
  { margin := bcMargin, sigmaHat := bcSigmaHat, etaMax := bcEtaMaxSimple }

end YMGap.BudgetConstants
