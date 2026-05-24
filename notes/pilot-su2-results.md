# SU(2) Pilot Results — Phase-3 Closure

> **Companion to** `computations/pilot_su2.py` (3.5).
>
> **Milestone.** 3.5 of `work_plan.md`. The final Phase-3 milestone, closing the SU(2) pilot at the framework level.

---

## 1. What the pilot reports

Per `docs/context.md` §7's five success criteria, plus a recommended quantitative threshold (work_plan 3.5's open question), `run_pilot()` returns a `PilotResult` with:

  1. **`crit_1_small_field_KP`** — every scale's small-field certificate has $\rho_{sf} > 0$, finite $K_{sf}$, and the small-field convergence flag set.
  2. **`crit_2_large_field_KP`** — analogous for large-field.
  3. **`crit_3_overlap_KP`** — every overlap certificate is finite and satisfies Proposition 7.1 (`proposition_7_1_satisfied` flag from 3.3).
  4. **`crit_4_delta_cap_summable`** — $\sum_k \Delta_\cap < \infty$ across the trajectory.
  5. **`crit_5_sigma_hat_positive_and_budget`** — every $\widehat{\sigma}_k > 0$ AND $\sum_k \eta_k < \widehat{\sigma}_0$.

Plus a quantitative threshold:

  - **`threshold_success`** — $\widehat{\sigma}_K \ge 0.5 \cdot \widehat{\sigma}_0$ (recommended at the Phase-3 kickoff: 50% retention over $K = 3$ RG steps).

And the overall flag:

  - **`pilot_succeeds`** = `all_five_pass AND threshold_success`.

---

## 2. Pilot result in the current analytic regime

Running `python -m computations.pilot_su2`:

```
K (RG steps)       : 3
Convention         : canonical
σ̂_0               : 1.0
σ̂_K (final)        : -inf
Σ_k Δ_∩            : inf
Σ_k η_k            : inf

(1) Small-field KP            : False
(2) Large-field KP            : True
(3) Overlap KP (P 7.1)        : False
(4) Σ Δ_∩ summable            : False
(5) σ̂ positive + budget       : False
All five pass?                : False

Quantitative threshold        : False

PILOT FAILS
```

**The default pilot fails honestly** because the post-3.1 Bałaban/Brydges-Federbush small-field upgrade makes $K_{sf}$ finite only below the current convergence threshold. With the canonical fiducial constants, $g_{\max} \approx 0.40$, while the default trajectory starts at $g_0 = 1.0$. Therefore $K_{sf} = \infty$, which propagates to $K_\cap$, $\Delta_\cap$, $\eta$, and the $\widehat{\sigma}$ budget.

The same validator can pass in a deliberately weak-coupling pilot, e.g. `run_pilot(g_0=0.1, sigma_hat_initial=10.0)`, where the tested trajectory stays inside the current convergence window. That is a useful framework check, not a full YM mass-gap claim.

---

## 3. What a real success would require

For the pilot to be a meaningful confirmation of the inductive step over a nontrivial trajectory, the remaining placeholders and convention risks must be resolved:

1. **3.2 large-field $K_{lf}(g_k)$** — character-expansion residual. Placeholder = 1.0.
2. **3.1 small-field coefficient $c_\lambda$** — currently fiducial $1/2$, pending direct Bałaban-paper extraction and normalization check.
3. **1.2/1.3 heat-kernel normalization** — the current heat-kernel-time discussion must be audited before any new character-expansion constant is treated as a probability bound.
4. **3.4 η-coupling** — actual polymer-expansion-residual factor relating $\Delta_\cap$ to $\eta$. Placeholder = 0.5.

When (1)–(4) are real, the pilot test becomes a genuine measurement of whether the inductive step closes for SU(2) at the recommended threshold $\widehat{\sigma}_K \ge 0.5 \widehat{\sigma}_0$.

---

## 4. Phase-3 summary

| Milestone | Deliverable | Status |
| --- | --- | --- |
| **3.0** | `Constructive/Rationals.lean` (Q' type) | Real, axiom-clean, lake-tested |
| **3.1** | Small-field KP `(ρ_sf, K_sf)` | Literature-grounded Bałaban/Brydges-Federbush synthesis; finite only below the current threshold; $c_\lambda$ fiducial |
| **3.2** | Large-field KP `(ρ_lf, K_lf)` | Framework; ρ_lf derived from 1.1/1.2, K_lf placeholder |
| **3.3** | Overlap KP via Prop 7.1 | Framework + buffer-glue mechanism, structurally verified |
| **3.4** | σ̂ trajectory + budget closure | Framework + Q'-boundary decision recorded (Q' suffices for the pilot) |
| **3.5** | Five-criteria validator | Runs end-to-end; default $g_0=1.0$ fails, weak-coupling test passes |

Inherited from Phase 1 / Phase 2:

- `[P2.1]` `domGlue_preserves_KP` sorry, parts (a) and (b): partial closure (the analytic precondition at SU(2) is supplied by 3.3; the Lean closure pending Q'-lift).
- `[P2.3-{sf,lf,cap,sigma}]` Lean sorries: open. Each requires the corresponding placeholder replacement and a Q'-lifted Lean term.

The Phase-3 framework is complete and integrated, but the analytic content is now partially non-placeholder and correctly exposes a convergence obstruction.

---

## 5. The Phase-3 → Phase-4 / Phase-5 handoff

What Phase 3 *did not* close:

- **The continuum limit** (`docs/outline.md` §13). The pilot runs at fixed lattice spacing; the continuum-limit modulus $\varepsilon(r, N)$ is not computed here.
- **The OS / Wightman reconstruction** (`docs/outline.md` §14). The inductive-step closure gives the area law, not the full Hilbert-space reconstruction.
- **The mass-gap claim** (`docs/outline.md` §12). Requires the inductive step to close in a real (non-placeholder) sense PLUS the spectral-gap transfer.

These are Phase 4 (codynamic transfer template) and Phase 5 (paper draft) content, respectively.

The Lean side has six open sorries (`[P2.1]` × 2 parts, `[P2.3-{sf,lf,cap,sigma}]`, `[P2.3] step_obligation_witness` assembled from the four). All are `[sorryAx]`-only, no `Classical.choice`, no `propext`, no `Quot.sound`. The construction is honest about what's open.

---

## 6. Recommended next moves (post-Phase-3)

Two parallel directions:

1. **Finish the Phase-3 upgrade pass.** First audit the heat-kernel/character-expansion normalization, then derive $K_{lf}(g_k)$ from the SU(2) character expansion. This is the last upstream placeholder feeding $K_\cap$.

2. **Close the Lean sorries.** For each `[P2.3-X]`, lift the placeholder rationals to Q' and construct a Lean term inhabiting `Obligation_X`. This is mechanical given (1). When all six sorries close, the SU(2) inductive step is machine-verified at the abstract type level — which, combined with the explicit numerical pilot from (1), is a serious-publishable artifact.

These two should be pursued together: a placeholder replacement landing in Python without a Q'-lift in Lean would be a weaker artifact.

---

## 7. Pointers

- Implementation: [`computations/pilot_su2.py`](../computations/pilot_su2.py).
- Tests: [`tests/test_pilot_su2.py`](../tests/test_pilot_su2.py).
- Figure: [`visualizations/pilot/su2/inductive-closure.svg`](../visualizations/pilot/su2/inductive-closure.svg).
- All upstream notes: [`notes/`](.).
- Lean ledger: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md).
- Specification: [`docs/context.md`](../docs/context.md) §7, [`docs/outline.md`](../docs/outline.md) §18.7.
