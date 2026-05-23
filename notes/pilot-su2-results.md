# SU(2) Pilot Results — Phase-3 Closure

> **Companion to** `computations/pilot_su2.py` (3.5).
>
> **Milestone.** 3.5 of `work_plan.md`. The final Phase-3 milestone, closing the SU(2) pilot at the framework level.

---

## 1. What the pilot reports

Per `docs/context.md` §7's five success criteria, plus a recommended quantitative threshold (work_plan 3.5's open question), `run_pilot()` returns a `PilotResult` with:

  1. **`crit_1_small_field_KP`** — every scale's small-field certificate has $\rho_{sf} > 0, K_{sf} \ge 0$.
  2. **`crit_2_large_field_KP`** — analogous for large-field.
  3. **`crit_3_overlap_KP`** — every overlap certificate satisfies Proposition 7.1 (`proposition_7_1_satisfied` flag from 3.3).
  4. **`crit_4_delta_cap_summable`** — $\sum_k \Delta_\cap < \infty$ across the trajectory.
  5. **`crit_5_sigma_hat_positive_and_budget`** — every $\widehat{\sigma}_k > 0$ AND $\sum_k \eta_k < \widehat{\sigma}_0$.

Plus a quantitative threshold:

  - **`threshold_success`** — $\widehat{\sigma}_K \ge 0.5 \cdot \widehat{\sigma}_0$ (recommended at the Phase-3 kickoff: 50% retention over $K = 3$ RG steps).

And the overall flag:

  - **`pilot_succeeds`** = `all_five_pass AND threshold_success`.

---

## 2. Pilot result in the placeholder regime (current state)

Running `python -m computations.pilot_su2`:

```
K                    : 3
Convention           : canonical
σ̂_0                  : 1.0
σ̂_K (final)          : 1.0
Σ_k Δ_∩              : 0.000000e+00
Σ_k η_k              : 0.000000e+00

(1) Small-field KP            : True
(2) Large-field KP            : True
(3) Overlap KP (P 7.1)        : True
(4) Σ Δ_∩ summable            : True
(5) σ̂ positive + budget       : True
All five pass?                : True

Quantitative threshold        : True

PILOT SUCCEEDS
```

**The pilot trivially succeeds** because of the upstream placeholder regime: $K_{sf} = K_{lf} = 1$ are constants (3.1, 3.2), so $K_\cap$ is constant (3.3), $\Delta_\cap = 0$ at every step, $\eta_k = 0$, and σ̂ doesn't degrade.

**This is not a real success**. It is a confirmation that the framework's five-criteria validator runs end-to-end, and that the structural relationships (Proposition 7.1, the inductive-step S1–S4 budget) hold by construction at the placeholder level.

---

## 3. What a real success would require

For the pilot to be a meaningful confirmation of the inductive step, the upstream placeholders must be replaced:

1. **3.1 small-field $K_{sf}(g_k)$** — actual cluster-expansion residual. Currently placeholder = 1.0. Bałaban-style derivation needed.
2. **3.1 small-field $\rho_{sf}(g_k)$** — actual spectral-gap-based rate. Currently placeholder $1/(2 g^2)$. Same.
3. **3.2 large-field $K_{lf}(g_k)$** — character-expansion residual. Placeholder = 1.0.
4. **3.4 η-coupling** — actual polymer-expansion-residual factor relating $\Delta_\cap$ to $\eta$. Placeholder = 0.5.

When (1)–(4) are real, the pilot test becomes a genuine measurement of whether the inductive step closes for SU(2) at the recommended threshold $\widehat{\sigma}_K \ge 0.5 \widehat{\sigma}_0$.

---

## 4. Phase-3 summary

| Milestone | Deliverable | Status |
| --- | --- | --- |
| **3.0** | `Constructive/Rationals.lean` (Q' type) | Real, axiom-clean, lake-tested |
| **3.1** | Small-field KP `(ρ_sf, K_sf)` | Framework + placeholder values |
| **3.2** | Large-field KP `(ρ_lf, K_lf)` | Framework; ρ_lf derived from 1.1/1.2, K_lf placeholder |
| **3.3** | Overlap KP via Prop 7.1 | Framework + buffer-glue mechanism, structurally verified |
| **3.4** | σ̂ trajectory + budget closure | Framework + Q'-boundary decision recorded (Q' suffices for the pilot) |
| **3.5** | Five-criteria validator | Framework + pilot runs end-to-end |

Inherited from Phase 1 / Phase 2:

- `[P2.1]` `domGlue_preserves_KP` sorry, parts (a) and (b): partial closure (the analytic precondition at SU(2) is supplied by 3.3; the Lean closure pending Q'-lift).
- `[P2.3-{sf,lf,cap,sigma}]` Lean sorries: open. Each requires the corresponding placeholder replacement and a Q'-lifted Lean term.

The Phase-3 framework is complete and integrated; the analytic content remains the open downstream work.

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

1. **Replace placeholders.** Pick one of 3.1's small-field or 3.2's K_lf and do the actual Bałaban derivation. Each replacement immediately makes its dependents non-trivial. Plug into the validator; observe whether the pilot still passes. If 3.4's σ̂-budget closes against the real values, **the inductive step is established for SU(2)** — the Clay-relevant claim, conditional only on the per-derivation correctness.

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
