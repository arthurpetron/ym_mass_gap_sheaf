# Change note: `MU_PLAQUETTE_4D` 16 → 1359141/25000 (≥ 20e) — SL.1 decision executed (2026-07-25)

> Drop-in for `notes/`.  Companion artifacts: modified
> `computations/large_field_kp.py`, `computations/fiducial_sensitivity.py`,
> `lean/YMGap/Sheaf/SU2KP.lean`, `lean/YMGap/Sheaf/PolymerDomination.lean`,
> and the re-pinned test files (`tests/test_large_field_kp.py`,
> `tests/test_kp_constants_lockstep.py`, `tests/test_overlap_kp.py`,
> `tests/test_fiducial_sensitivity.py`, `tests/test_m_0_tornado.py`,
> `tests/test_m_0_bootstrap.py`).  Value ledger: `mu20_summary.json`.

## 1. What changed and why

`MU_PLAQUETTE_4D` was the "Seiler 5d − 4 = 16" literature-shape fiducial.
The SL.1 exact enumeration (`computations/plaquette_connectivity.py`,
pinned by `tests/test_plaquette_connectivity.py`) established:

* **5d − 4 matches NO natural plaquette-adjacency notion on Z^d at any
  d.**  Its d = 4 value 16 coincides with the non-coplanar
  edge-neighbour count 8(d − 2) at d = 4 only (d = 3: 8 vs 11; d = 5:
  24 vs 21).  A coincidence, not a formula.
* **The code-consumed count** N_n(P₀) = #{edge-connected plaquette
  polymers, |X| = n, P₀ ∈ X} has exact values 1, 20, 458, 11132,
  280175 (n ≤ 5) with one-step growth ratios 20.0, 22.9, 24.3, 25.2 —
  above 16 from n = 2 onward.  `N_n ≤ 16^n` holds for n ≤ 5 but is not
  asymptotically defensible (naive extrapolation: first violation near
  n ≈ 8).
* **What IS a theorem:** the plaquette edge-adjacency graph has
  max-degree exactly Δ = 8d − 12 = 20 at d = 4 (enumeration-certified),
  so the Brydges–Federbush universal bound gives N_n ≤ (eΔ)^n = (20e)^n.

**New default** (exact-rational repo style; validity of `N_n ≤ μ^n`
requires μ ≥ the true growth constant, so μ must enter as a rational
UPPER bound on 20e):

```
MU_PLAQUETTE_4D_RATIONAL = Fraction(1359141, 25000)   # = 20 × 2718282/1000000 = 54.36564
MU_PLAQUETTE_4D          = float(MU_PLAQUETTE_4D_RATIONAL)
SEILER_5D_MINUS_4_LEGACY = 16.0                       # comparison sweeps ONLY
```

**≥ 20e proof:** e = 2.718281828… < 2.718282 = 2718282/10⁶, hence
20e < 20·2718282/10⁶ = 1359141/25000.  Certified in exact rational
arithmetic by `tests/test_large_field_kp.py::TestMuPlaquetteGe20eGuard`
via the factorial-series certificate e ≤ Σ_{k≤15} 1/k! + 1/(15!·14)
(error < 1e-12 against the majorant's ≈ 3.4e-6 slack).  The guard also
pins the float image (Fraction(float) is exact) and asserts the legacy
16 < 20e can never be re-adopted as "BF-conservative".  Module status:
**DERIVED bound**, no longer LITERATURE-SHAPE; provenance →
`computations/plaquette_connectivity.py` and `notes/fiducials_notes.md` §3.

## 2. Old → new value table (canonical convention unless noted)

| Quantity | old (μ = 16) | new (μ = 1359141/25000) |
| --- | --- | --- |
| `MU_PLAQUETTE_4D` | 16.0 | 54.36564 (= 1359141/25000 ≥ 20e) |
| `MU_PLAQUETTE_4D_LOG` | 2.7726 | 3.9959 |
| `convergence_threshold_g_lf` (canonical) | 0.424549 | **0.373289** (−12.07%) |
| `convergence_threshold_g_lf` (Wilson) | 0.849098 | 0.746579 |
| K_lf(g = 0.20) | 4.6042e-07 | 1.5645e-06 |
| K_lf(g = 0.30) | 0.01562403 | **0.05515448** |
| K_lf(g = 0.35) | 0.16328945 | 0.91187117 |
| K_lf(g = 0.40) | 1.43876432 | ∞ (0.40 > new threshold) |
| K_lf(Wilson g = 0.50) | 3.933e-04 | 1.3379e-03 |
| ρ_lf(g), eps_lf | unchanged | unchanged (μ-independent: ρ_lf = −log Z_t) |
| q(g = 0.30) = μ·Z_t^upper | 0.0153837 | 0.0522715 |
| Pilot Σ_k η_k (g₀ = 0.30, K = 3, σ̂₀ = 1) | 7.9511e-04 | **2.3932e-03** |
| Pilot budget closes? | True | **True (unchanged)** |
| Pilot m₀ = √(1 − Ση) | 0.999602 | **0.998803** |
| Quotable rational m₀ floor (/1000) | 999/1000 | **998/1000** |
| `max_g0_closure` (default fiducials) | 0.413208 | 0.365503 |
| Union-bound looseness at g = 0.30 | ≈ 1.0155 | 1.0549 (conjecture-7.4 bound 2 intact) |
| Tornado ±20% m₀ envelope | ⊂ (0.999, 1) | [0.99840, 0.99904] ⊂ (0.998, 1) |
| Tornado most-sensitive fiducial | c_λ | A_min > μ_plaq > c_polymer > c_λ |
| Bootstrap 5th-pct m₀ (n=2000, seed=0) | ≥ 950/1000 headline | 0.994056 → 994/1000 (headline ≥ 950 intact) |

## 3. Pilot-closure verdict: UNCHANGED — with one headline correction

**Closure holds, unchanged.**  At the canonical wire-in (g₀ = 0.30,
K = 3, σ̂₀ = 1) the trajectory g_k ≈ 0.3000 → 0.3013 sits well inside
BOTH windows — the new lf-window g_max^lf = 0.3733 and the sf-window
g_max^sf = 0.4935 — so every K_sf, K_lf on the trajectory is finite and
Σ_k η_k = 2.393e-3 ≪ σ̂₀ = 1 (margin ≈ 418×, was ≈ 1258×).

**Binding-window argument, stated precisely.**  At the operating point
the closure boolean is nowhere near either threshold; what the μ flip
does move is the *edge* of the pilot window: `max_g0_closure` drops
0.4132 → 0.3655, and the binding constraint at that edge is now the
**large-field** window (0.3733, minus trajectory drift), no longer the
small-field one.  The prior SL.1 shorthand "sf window binds" is correct
for the closure *at g₀ = 0.30* only in the weak sense that both windows
clear it comfortably; at the window edge the lf-side now binds.  Since
the project pins the pilot at g₀ = 0.30 (Lean `CANONICAL_G = 3/10`),
closure is unchanged.

**Surprise to report loudly (not a closure break):** the manuscript
headline m₀ moves in the 4th decimal: 0.999602 → 0.998803, so the
Q'-quotable floor drops **999/1000 → 998/1000** (the same value the
pre-Casimir-gap c_λ = 1/2 era quoted).  The tornado headline test
asserting m₀ ∈ (0.999, 1) failed at baseline and was re-pinned to
(0.998, 1); any Lean/manuscript statement quoting `m_0 ≥ 999/1000`
must be re-pinned to 998/1000.  The bootstrap robust bound
(5th percentile 0.9941 → 994/1000) still clears the ≥ 950/1000 headline.

## 4. Consumers audited (grep 2026-07-25, full repo)

`MU_PLAQUETTE_4D` readers: `computations/large_field_kp.py` (definition
+ `compute_large_field_kp` / `eps_lf` / `first_few_rg_steps` /
`convergence_threshold_g_lf` defaults), `overlap_kp.py`
(`compute_overlap_kp` / `delta_cap` / looseness helpers),
`sigma_hat_trajectory.py` (`compute_eta` / `sigma_hat_trajectory`
defaults), `fiducial_sensitivity.py` (`sweep_mu_plaq` /
`max_g0_closure` / `c_lambda_pilot_tolerance_threshold`),
`m_0_tornado.py` (registry baseline), `m_0_bootstrap.py` (envelope
baseline; envelope [10, 55] still contains 54.36564 — barely; consider
widening the high edge if μ is ever loosened further),
`plaquette_connectivity.py` (docstring), `scripts/su3_closure_spike.py`
(`MU_PLAQ = lf.MU_PLAQUETTE_4D` — inherits the new value; its `# 16`
comment is stale), `scripts/uniform_bound_sweep.py` (imports the
module; inherits), and tests.  All inherit the new default through the
single constant; only the files listed in the header needed edits.

## 5. Lean re-pins (SU2KP.lean, PolymerDomination.lean)

μ-dependent Q' constants were re-pinned with conservative upward
rounding; all `by decide` arithmetic re-verified in exact rationals
(Python `Fraction`, see `test_lean_bf_derivation_arithmetic_canonical`):

| Lean constant | old | new | check |
| --- | --- | --- | --- |
| `SU2KP.q_canonical_upper` | 154/10000 | 523/10000 | 0.0523 ≥ q = 0.052271 ✓; q < 1 ✓ |
| `SU2KP.K_lf_canonical` | 16/1000 | 56/1000 | 0.056 ≥ K_lf = 0.055154 ✓; q ≤ K(1−q): 0.0523 ≤ 0.0530712 ✓ |
| `SU2KP.q_wilson_upper` | 4/10000 | 14/10000 | 0.0014 ≥ 0.0013361 ✓ |
| `SU2KP.K_lf_wilson` | 1/1000 | 2/1000 | 0.002 ≥ 0.0013379 ✓; 0.0014 ≤ 0.0019972 ✓ |
| `PolymerDomination.K_lf_pilot` | 2/125 (= 0.016) | 7/125 (= 0.056) | dominance 7·10 ≤ 11·125 ✓ |

Unchanged (μ-independent): `rho_lf_canonical = 6947/1000`,
`rho_lf_wilson = 10613/1000`, `rho_lf_le_rho_sf_canonical`, all
small-field constants, `mu_upper_canonical = 31/10` and
`gap_canonical = 157/30` (those bound the *small-field* μ = log 8e).
**Caught by the new lockstep tests:** the old `K_lf_pilot = 2/125` and
`K_lf_canonical = 16/1000` become UNSOUND upper bounds under the new μ
— exactly the silent-drift class the lockstep suite exists for; the
suite now pins the large-field side too (previously sf-only).
`by decide` proofs must still be re-elaborated by `lake build` on the
repo side (not runnable in this container); the arithmetic they check
is verified exactly here.

## 6. Test re-pins (mechanical consequences of the flip)

* `test_large_field_kp.py`: threshold pin 0.42–0.43 → 0.3732–0.3734;
  near-threshold K sample 0.40 → 0.36; BF-vs-default direction tests
  rewritten (default now IS the BF majorant; legacy comparisons keep the
  old inequalities); **new** `TestMuPlaquetteGe20eGuard` (4 tests,
  exact-rational ≥ 20e guard).
* `test_kp_constants_lockstep.py`: small-field pins unchanged (25/3
  etc. all μ-independent); **added** 6 large-field lockstep tests
  (μ ground-truth rational; Lean K_lf/q canonical+Wilson conservative
  bounds; exact BF decide-arithmetic; PolymerDomination staleness guard).
* `test_overlap_kp.py`: looseness-at-wire-in bound 1.05 → 1.06
  (measured 1.0549); joint-convergent-regime scan grids 0.05–0.41 →
  0.05–0.36 (canonical), 0.10–0.84 → 0.10–0.73 (Wilson).
* `test_fiducial_sensitivity.py`: "conservative shrinks window" tests
  re-oriented (default is now the largest defensible μ); `max_g0`
  re-pinned to (0.36, 0.38).
* `test_m_0_tornado.py`: μ baseline 16 → `MU_PLAQUETTE_4D`; headline
  envelope (0.999, 1) → (0.998, 1); sensitivity-ordering test replaces
  "c_λ dominates" (now A_min > μ_plaq > c_polymer > c_λ, spread < 2×).
* `test_m_0_bootstrap.py`: baseline comment 0.9996 → 0.9988 (assertions
  unchanged and passing).

## 7. Test results (all green, 2026-07-25)

* `mu20/tests` (mirrored + re-pinned, 8 files): **195 passed**.
* Regression floor `/home/claude/ym_dp6/tests`: **23 passed**.
* SL.1 enumeration suite `/home/claude/sl1`: **15 passed**.
