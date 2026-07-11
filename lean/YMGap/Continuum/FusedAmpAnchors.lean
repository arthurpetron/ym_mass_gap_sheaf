/-
`FusedAmpAnchors` — Milestone 14.2 OPENED (the quantitative frame): the
RAW derived amplitudes at the pilot truncation, computed as kernel facts —
pinning exactly what the defect identity must cancel.

# The point (honest bookkeeping before the attack)

The derived channel amplitudes `fusedAmp N s` bound the RAW blocked
coefficients.  They are NOT the defect amplitudes: the defect is
blocked-MINUS-free, and only its deviation enters the `Σ ≤ 6` budget.
The kernel facts below quantify the gap: at `N = 3` the raw channel-0
amplitude alone is `30` (= `Σ_a dimQ a²` over the diagonal pairs) — five
times the whole budget.  So Milestone 14.2's free-counterterm subtraction
must cancel the leading (free) part of every channel EXACTLY, leaving a
deviation whose amplitudes sum under `6`; the anchors below are the
machine-checked record of the cancellation scale required.  If the
subtracted amplitudes still exceed the budget at every reasonable
truncation, that is the REFUTATION to bank (Phase 14 risk register).

# What is delivered (kernel `decide`, axiom-FREE)

  * `fusedAmp_N3_ch0` — `fusedAmp 3 0 = 30` (diagonal pairs, `Σ dimQ²`);
  * `fusedAmp_N3_ch1_le` / channel anchors — the raw amplitude ledger at
    the pilot truncation;
  * `raw_budget_fails` — the RAW amplitudes provably violate the `Σ ≤ 6`
    certificate (the subtraction is NOT optional — machine-checked).

# Constructive contract (`lean/AGENTS.md` Rules 1, 6, 8)

Mathlib-free; pure `Q'` / `Nat` core.  Kernel `decide` on exact rationals
only.  Gated with `#print axioms`.
-/

import YMGap.Continuum.FusedChannelAll
import YMGap.Continuum.HKChannelList

namespace YMGap.Continuum.FusedAmpAnchors

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.TaylorModel
open YMGap.Continuum.HKChannelList
open YMGap.Continuum.FusedChannelAll

/-- The raw channel-0 amplitude at `N = 3`: the diagonal character sum
`Σ_{a≤3} dimQ a² = 1 + 4 + 9 + 16 = 30`. -/
theorem fusedAmp_N3_ch0 : (fusedAmp 3 0).eqv (Q'.ofNat 30) := by decide

/-- The raw channel-1 amplitude at `N = 3` (neighbour pairs
`2·(1·2 + 2·3 + 3·4) = 40`). -/
theorem fusedAmp_N3_ch1 : (fusedAmp 3 1).eqv (Q'.ofNat 40) := by decide

/-- **`raw_budget_fails` (kernel `decide` — the subtraction is NOT
optional).**  The raw derived amplitudes at the pilot truncation provably
violate the `Σ ≤ 6` certificate already from channel 0 alone: the defect
identity (blocked − free) of Milestone 14.2 must cancel the free part of
every channel before the budget can close. -/
theorem raw_budget_fails :
    coeffLeB [0, 0, fusedAmp 3 0] sixUsq = false := by decide

end YMGap.Continuum.FusedAmpAnchors

/-! ## Axiom-dependency gates (AGENTS.md Rule 1) -/

#print axioms YMGap.Continuum.FusedAmpAnchors.fusedAmp_N3_ch0
#print axioms YMGap.Continuum.FusedAmpAnchors.fusedAmp_N3_ch1
#print axioms YMGap.Continuum.FusedAmpAnchors.raw_budget_fails
