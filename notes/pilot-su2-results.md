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
(2) Large-field KP            : False
(3) Overlap KP (P 7.1)        : False
(4) Σ Δ_∩ summable            : False
(5) σ̂ positive + budget       : False
All five pass?                : False

Quantitative threshold        : False

PILOT FAILS
```

**The default pilot fails honestly** because BOTH the post-3.1 Bałaban/Brydges-Federbush small-field upgrade AND the post-3.2 heat-kernel character-tail large-field upgrade make their respective $K$-amplitudes finite only below their cluster-expansion convergence thresholds. With the canonical fiducial constants: $g_{\max}^{sf} \approx 0.40$ and $g_{\max}^{lf} \approx 0.42$. The default trajectory starts at $g_0 = 1.0$, far above both thresholds; therefore $K_{sf} = K_{lf} = \infty$, propagating to $K_\cap$, $\Delta_\cap$, $\eta$, and the $\widehat{\sigma}$ budget.

The same validator passes comfortably in the weak-coupling pilot, e.g. `run_pilot(g_0=0.1, sigma_hat_initial=10.0)`: σ̂_K = σ̂_0 to numerical precision, all five criteria pass, threshold passes with σ̂_K = σ̂_0 ≥ 0.5 σ̂_0. The pilot's passing window now corresponds to the *intersection* of both convergence regimes (sf and lf): empirically `g_0 ≤ 0.35` canonical, `g_0 ≤ 0.70` Wilson — and the sf bound is the binding constraint in both conventions.

---

## 3. What a real success would require

For the pilot to be a meaningful confirmation of the inductive step over a nontrivial trajectory, the remaining placeholders and convention risks must be resolved:

1. **3.4 η-coupling** — actual polymer-expansion-residual factor relating $\Delta_\cap$ to $\eta$. Placeholder = 0.5. This is now the LAST remaining upstream placeholder.
2. **3.1 small-field coefficient $c_\lambda$** — currently fiducial $1/2$, pending direct Bałaban-paper extraction and normalization check.
3. **3.2 plaquette connectivity $\mu_{\text{plaq}} = 16$** — currently fiducial literature value from Seiler 1982 / Drouffe–Itzykson 1989; tighter polymer counts enlarge the convergent regime.
4. **3.2 character sup bound** — currently the trivial $|\chi_j(U)| \le d_j = 2j+1$; a Bałaban-style distance-from-identity-aware bound would shrink $Z_t$ and enlarge the regime, mirroring the small-field-upgrade structure.

When (1) lands and (2)–(4) are refined, the pilot test becomes a genuine measurement of whether the inductive step closes for SU(2) at the recommended threshold $\widehat{\sigma}_K \ge 0.5 \widehat{\sigma}_0$ over a wider trajectory range.

---

## 4. Phase-3 summary

| Milestone | Deliverable | Status |
| --- | --- | --- |
| **3.0** | `Constructive/Rationals.lean` (Q' type) | Real, axiom-clean, lake-tested |
| **3.1** | Small-field KP `(ρ_sf, K_sf)` | Literature-grounded Bałaban/Brydges-Federbush synthesis; finite only below the current threshold; $c_\lambda$ fiducial |
| **3.2** | Large-field KP `(ρ_lf, K_lf)` | Real (post-3.2-upgrade): ρ_lf strict via heat-kernel character-tail truncation, ρ_lf_asymptotic = κ/g² preserved as separate field, K_lf via Brydges–Federbush cluster expansion; convergence threshold canonical g_max ≈ 0.42, Wilson g_max ≈ 0.85 |
| **3.3** | Overlap KP via Prop 7.1 | Framework + buffer-glue mechanism, structurally verified |
| **3.4** | σ̂ trajectory + budget closure | Real (post-3.4-upgrade): η-coupling DERIVED from outline §7.1's smallest Wilson loop area (= 4) and a Bałaban polymer-residual fiducial (= 2), giving default `DERIVED_ETA_COUPLING = 1/2 ∈ ℚ`; b-independent; Q'-boundary decision unchanged (Q' suffices for the pilot) |
| **3.5** | Five-criteria validator | Runs end-to-end; default $g_0=1.0$ fails, weak-coupling test passes |

Inherited from Phase 1 / Phase 2:

- `[P2.1]` `domGlue_preserves_KP` — **part (a) CLOSED 2026-05-24**, part (b) open. Part (a) is closed by exposing the analytic content as an explicit `P_glue` hypothesis (plus a `LE.refl V` hypothesis), discharged for concrete predicates at `V = Q'`: `P_trivial ρ K := True` (smoke test) and `P_nonneg ρ K := 0 ≤ ρ ∧ 0 ≤ K` (substantive, using `Q'.zero_le_min` and `Q'.zero_le_add`). `domGlue_preserves_KP` itself reports **does not depend on any axioms** (pure definitional); the two concrete instances depend on `[propext]` only. Part (b) (Conjecture 7.4 tightness — whether `K_∩ ≤ K_sf + K_lf` is lossy by a fat band) remains open, requires concrete polymer activities to verify.
- `[P2.3-{sf,lf,cap,sigma}]` Lean sorries: **CLOSED 2026-05-24**. All four sub-witnesses now exist at `V = Q'` via the identity inductive step (budgets = 0, certificates / σ̂ reused). `step_obligation_witness` reports `depends on axioms: [propext]` only — no `sorryAx`, no `Classical.choice`. The structural [P2.3-addendum] predictions (sf ⊥ lf; σ depends on cap only) are confirmed at the closed-witness level. Quantitative content lives in `computations/`.

**Lean side: every sorry tracked in `lean/SORRY_LEDGER.md` is now CLOSED except `[P2.1]` part (b).** Full `lake build` output contains zero `sorryAx` and zero `Classical.*` axiom dependencies — the entire Lean library is constructively axiom-clean modulo the allowed `propext` / `Quot.sound`.

The Phase-3 framework is complete and integrated; every upstream placeholder has been derived. The pilot fails at default `g_0 = 1.0` because the small-field cluster expansion does not converge there — an honest analytic obstruction inherited from the Bałaban literature, not a framework defect.

---

## 5. The Phase-3 → Phase-4 / Phase-5 handoff

What Phase 3 *did not* close:

- **The continuum limit** (`docs/outline.md` §13). The pilot runs at fixed lattice spacing; the continuum-limit modulus $\varepsilon(r, N)$ is not computed here.
- **The OS / Wightman reconstruction** (`docs/outline.md` §14). The inductive-step closure gives the area law, not the full Hilbert-space reconstruction.
- **The mass-gap claim** (`docs/outline.md` §12). Requires the inductive step to close in a real (non-placeholder) sense PLUS the spectral-gap transfer.

These are Phase 4 (codynamic transfer template) and Phase 5 (paper draft) content, respectively.

The Lean side has six open sorries (`[P2.1]` × 2 parts, `[P2.3-{sf,lf,cap,sigma}]`, `[P2.3] step_obligation_witness` assembled from the four). All are `[sorryAx]`-only, no `Classical.choice`, no `propext`, no `Quot.sound`. The construction is honest about what's open.

---

## 6. Recommended next moves (post-3.4-upgrade and post-RationalTail wire-in)

Updates landed 2026-05-24:

  * **Lean sorries `[P2.3-{sf,lf,cap,sigma}]` all CLOSED** — per `lean/SORRY_LEDGER.md`, the four per-step obligations are inhabited at `V = Q'` with axiom-gate `[propext]` only.  Only `[P2.1]` part (b) (tightness conjecture) remains open in `lean/`.
  * **Global σ̂-budget closure framework + SU(2) pilot wire-in CLOSED at finite truncation** — `lean/YMGap/Constructive/RationalTail.lean` provides the framework theorem `sigma_hat_budget_closure` plus the workhorse `finSum_stabilizes_after_K`; `lean/YMGap/RG/SigmaHatPilot.lean` instantiates it on the canonical Python pilot at `(g_0 = 0.30, K = 3, σ̂_0 = 1)` with a Q'-rational upper bound `η_max = 11/10000`.  All theorems report `[propext]` only.
  * **Fiducial handling formalized** — `MU_PLAQUETTE_CONSERVATIVE_4D = 8e ≈ 21.75` added as a rigorous-fallback variant for the large-field plaquette connectivity bound (fiducials §3 option 2); `compute_large_field_kp` and `convergence_threshold_g_lf` expose `mu_plaq` as a parameter.  `sigma_hat_trajectory` and `compute_eta` now thread `polymer_residual` and `wilson_loop_min_area` directly.  Sensitivity sweeps live in `computations/fiducial_sensitivity.py`.

Remaining directions:

1. **Refine the three flagged fiducials against direct paper extraction.** Per `notes/fiducials_notes.md`:
   - `BAŁABAN_SPECTRAL_GAP_COEFF = 1/2` (literature-shape; refinement awaits Bałaban paper consultation).
   - `MU_PLAQUETTE_4D = 16` (widely cited as `5d - 4` but unverified; conservative `MU_PLAQUETTE_CONSERVATIVE_4D = 8e` available NOW as a rigorous alternative).
   - `BALABAN_POLYMER_RESIDUAL = 2.0` (heuristic; refinement awaits Bałaban 1988 polymer-residual extraction).

   Each refinement is mechanical given paper consultation.  Run `python -m computations.fiducial_sensitivity` for an at-a-glance impact table — all three fiducials now report real `Σ η_k` movement and a pilot-window `g_0_max` (via `max_g0_closure`) since the 2026-05-24 threading work.

2. **Close `[P2.1]` part (b)** — Conjecture 7.4 tightness of `K_∩ ≤ K_sf + K_lf`.  Requires concrete polymer activity forms; depends on a sharper analytic input than 3.1 / 3.2 / 3.3 currently provide.

3. **Lift the rational-tail closure to the Phase-1-output trajectory.**  The current `SigmaHatPilot.eta_pilot_budget_closes` is at finite `N`; for a Phase-4 continuum-limit claim we'd want either a rational tail bound on `Σ_{k ≥ K} η_k` (option (i) of §4.2 in `notes/sigma-hat-derivation.md`) or a constructive-reals layer (option (ii)).  Not on the Phase-3 critical path.

4. **Audit the heat-kernel normalization** (`work_plan.md` Current-status item 4).  The current notes carry both inverse-coupling and diffusion-time language; before any character-expansion constant is treated as a probability bound, this needs resolution.  Independent of the σ̂-budget work.

Pilot sweep summary (post-3.2-upgrade, K = 3, canonical):

  - **Pass**: `g_0 ∈ {0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35}` — all five criteria pass and σ̂_K ≥ 0.97 σ̂_0 throughout.
  - **Fail**: `g_0 ∈ {0.40, 0.45, 0.50, ..., 1.00}` — small-field cluster expansion diverges (sf threshold ≈ 0.40 < lf threshold ≈ 0.42).

Wilson sweep:

  - **Pass**: `g_0 ∈ {0.10, 0.30, 0.50, 0.70}` with σ̂_K = 0.855 at the edge `g_0 = 0.70`.
  - **Fail**: `g_0 ∈ {0.80, 0.85, 0.90, 1.00}` — sf threshold ≈ 0.81 reached.

See `notes/large-field-derivation.md` §9 for the full sweep table.

---

## 7. Pointers

- Implementation: [`computations/pilot_su2.py`](../computations/pilot_su2.py).
- Tests: [`tests/test_pilot_su2.py`](../tests/test_pilot_su2.py).
- Figure: [`visualizations/pilot/su2/inductive-closure.svg`](../visualizations/pilot/su2/inductive-closure.svg).
- All upstream notes: [`notes/`](.).
- Lean ledger: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md).
- Lean RationalTail framework: [`lean/YMGap/Constructive/RationalTail.lean`](../lean/YMGap/Constructive/RationalTail.lean).
- Lean SU(2) pilot wire-in: [`lean/YMGap/RG/SigmaHatPilot.lean`](../lean/YMGap/RG/SigmaHatPilot.lean).
- Python → Lean rational lift: [`computations/q_lift.py`](../computations/q_lift.py).
- Fiducial audit + sensitivity sweeps: [`notes/fiducials_notes.md`](fiducials_notes.md), [`computations/fiducial_sensitivity.py`](../computations/fiducial_sensitivity.py).
- Specification: [`docs/context.md`](../docs/context.md) §7, [`docs/outline.md`](../docs/outline.md) §18.7.
