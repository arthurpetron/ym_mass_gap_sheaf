# The Block-Spin Step — Prose Companion

> **Companion to** `formal/block-spin-morphism.tex` (formal statements) and `lean/YMGap/Sheaf/`, `lean/YMGap/RG/` (Lean formalization).
>
> **Milestone.** 2.3 of `work_plan.md` (Phase 2, block-spin morphism).
>
> This document is the prose argument for the refinement of the block-spin step from a bare typed seam (Milestone 2.2's `StepType`) to a refined type carrying the four conditions of `docs/context.md` §3.3, abstract over per-step budget functions.

---

## 1. What 2.3 adds on top of 2.2

Milestone 2.2 defined the inductive state `ℐ_k` and exposed a deliberately-bare `StepType = ℐ_k → ℐ_{k+1}` as the clean handoff. That seam is the simplest possible expression of "the step goes from one scale to the next"; it carries no degradation budget and no information about what makes the step *valid*.

Milestone 2.3 refines that seam in two ways:

1. **Type-level refinement.** The new `StepTypeWithBudget` (`formal/block-spin-morphism.tex` Definition 5.2 = `def:step-type-with-budget`) takes a *valid* input state to a *valid* output state, and additionally carries proofs of the four conditions S1–S4 of `docs/context.md` §3.3 — each a per-step inequality relating scale-k and scale-(k+1) quantities via a budget value at scale k.

2. **Categorical-level expansion.** Per `work_plan.md` Milestone 2.3, we name the block-spin map $T_b$ as a site morphism (Definition 2.3 = `def:site-morphism`), the pushforward $(T_b)_*$ on $\mathcal{A}_k$ and $\mathcal{S}_k$ (Definitions 3.1–3.2), and the dimensional-rescaling 2-cell $\Theta_k$ as a separate typed object (Definition 4.1 = `def:two-cell-theta`, per the open-question recommendation).

Both refinements stay strictly at the *type* level. We do not in 2.3 exhibit any term inhabiting `StepTypeWithBudget`, and we do not supply concrete budget functions. Both are 3.x.

## 2. The four conditions, in plain English

For an input state `ℐ_k` and the step's output `ℐ_{k+1} = T_b(ℐ_k)`, with budget functions $\varepsilon_{sf}, \varepsilon_{lf}, \Delta_\cap, \eta$ evaluated at $(b, g_k)$:

- **S1: small-field $\rho$-budget.** The small-field exponential-decay rate degrades by at most $\varepsilon_{sf}(b, g_k)$ per RG step:
  $$\rho_{sf, k+1} \ge \rho_{sf, k} - \varepsilon_{sf}(b, g_k).$$

- **S2: large-field $\rho$-budget.** Analogously for the heat-kernel-driven large-field rate:
  $$\rho_{lf, k+1} \ge \rho_{lf, k} - \varepsilon_{lf}(b, g_k).$$

- **S3: overlap $K$-budget.** The buffer amplitude *grows* (it does not decay) by at most $\Delta_\cap(b, g_k)$ per step:
  $$K_{\cap, k+1} \le K_{\cap, k} + \Delta_\cap(b, g_k).$$

- **S4: string-tension budget ($= \Theta_k$).** The renormalized string tension (σ-3 sense) degrades by at most $\eta(b, g_k)$:
  $$\widehat{\sigma}_{k+1} \ge \widehat{\sigma}_k - \eta(b, g_k).$$

S4 is exactly the 2-cell $\Theta_k$ of `outline.md` §10.4: a typed witness of the σ̂-transport from scale k to scale k+1. We expose it as a separate object — `TwoCellTheta` in the Lean — so future agents can reason about the σ̂-transport in isolation.

## 3. Why the budget is abstract here

Each of the four budget functions is the joint output of a regime-specific analytic calculation:

| Budget | Source milestone | What it encodes |
| --- | --- | --- |
| $\varepsilon_{sf}(b, g_k)$ | 3.1 (small-field KP constants) | Gaussian-tail / perturbative-expansion bound on the change in small-field $\rho$ under one block-spin step. |
| $\varepsilon_{lf}(b, g_k)$ | 3.2 (large-field KP constants) | Character-expansion / heat-kernel-stability bound on the change in large-field $\rho$. |
| $\Delta_\cap(b, g_k)$ | 3.3 (overlap KP constants) | Union-bound + buffer-glue analysis (carrying 2.1's `domGlue_preserves_KP` sorry and Conjecture 7.4's tightness). |
| $\eta(b, g_k)$ | 3.4 (string-tension 2-cell budget) | Pushforward + dimensional-rescaling analysis, plus whatever margin the global budget closure of `outline.md` §10.4 leaves available. |

Pinning any of these now would (a) lock in a form before the regime-specific calculation that produces it, and (b) potentially conflict with what those regime calculations actually deliver. 2.3 therefore states the *type* with the budgets as parameters; 3.x supplies them.

## 4. The carry-uncertainty chain: where 2.1's sorry surfaces

Building on the 2.2 carry-uncertainty discussion: a term inhabiting `StepTypeWithBudget` must, given a valid input `ℐ_k`, produce a *valid* output `ℐ_{k+1}`. Valid is V1 ∧ V2 ∧ V3 (the self-contained 2.2 predicate). The V2 conjuncts demand that the three output certificates' KP predicates hold; the V3 conjuncts demand the output buffer's $\rho_{\cap, k+1}$ and $K_{\cap, k+1}$ relate to the output $\rho_{sf, k+1}, \rho_{lf, k+1}, K_{sf, k+1}, K_{lf, k+1}$ per `sheaf-framework.tex` Proposition 7.1.

If the term constructs the output buffer certificate `c_cap_{k+1}` from `c_sf_{k+1}, c_lf_{k+1}` via `domGlue_preserves_KP` (the natural choice, since that theorem is precisely the buffer-glue mechanism), then:

- The output V2-cap conjunct (the regime predicate holds for the new buffer constants) inherits `domGlue_preserves_KP`'s `sorryAx` dependency, owed by 3.3.
- The output V3 buffer-glue inequality $K_{\cap, k+1} \le K_{sf, k+1} + K_{lf, k+1}$ inherits the tightness obligation of `sheaf-framework.tex` Conjecture 7.4, also owed by 3.3.

This is the design intent: the 2.3 obligation honestly carries the 2.1 open obligations through. A future agent reading "`StepTypeWithBudget` has a term, what's its axiom set?" will see, transitively, the `sorryAx` from 2.1 — not because 2.3 invented it but because the obligation chain genuinely depends on 2.1.

## 4a. The P2.3-addendum decomposition

Subsequent to the original P2.3 close, the atomic `StepObligation` was decomposed into four per-milestone sub-obligations (`formal/block-spin-morphism.tex` Definition 6.1):

- **`Obligation_sf`** — closed by 3.1. Independent.
- **`Obligation_lf`** — closed by 3.2. Independent (takes no `sf_part`).
- **`Obligation_cap`** — closed by 3.3. Takes `sf_part`, `lf_part`.
- **`Obligation_sigma`** — closed by 3.4. Takes `cap_part`.

The atomic form is recovered as a `Σ'` over the four parts (`StepObligation_decomposed`); the original `StepObligation` becomes an alias. Each Phase-3 milestone now has a precisely-scoped Lean obligation, with the analytic coupling exposed at the type level (cap depends on sf and lf; sigma depends on cap only).

**Encoded-but-unverified.** The dependency graph — sf ⊥ lf, sigma-via-cap-only — is a structural prediction about analytic derivations that don't exist yet. It's *self-correcting*: if 3.1/3.2 actually couple, `Obligation_lf` will not close standalone and the type will need a coupling edge added; if 3.4 needs direct ε-access, `Obligation_sigma`'s signature will need to be widened. The audit point is exactly when each owning milestone closes. See `formal/block-spin-morphism.tex` Remark 6.2 and `lean/SORRY_LEDGER.md` `[P2.3-addendum]`.

## 5. The 2.3 / 3.x boundary, made explicit

Five things 2.3 produces:

1. The site morphism $T_b$ (categorical-level definition).
2. The pushforward $(T_b)_*$ on $\mathcal{A}_k$ and $\mathcal{S}_k$.
3. The 2-cell $\Theta_k$ as a separate typed object.
4. The refined `StepTypeWithBudget` carrying S1–S4 with abstract budget.
5. The four per-milestone sub-obligations (`Obligation_sf`, `Obligation_lf`, `Obligation_cap`, `Obligation_sigma`) and their atomic recombination `StepObligation_decomposed`, plus four `sorry`'d witness placeholders — one per Phase-3 milestone.

Six things 2.3 does **not** produce:

1. A term inhabiting `StepTypeWithBudget`, abstract or concrete (TRAP 1: inhabitation).
2. Concrete forms of any of $\varepsilon_{sf}, \varepsilon_{lf}, \Delta_\cap, \eta$ — these are 3.1, 3.2, 3.3, 3.4 respectively.
3. The Wilson / Migdal–Kadanoff / block-spin-with-projection averaging procedure underlying $T_b$ — a program-level choice fixed in 3.x.
4. Any claim that $\sum_k \Delta_\cap(b, g_k) < \infty$ or $\sum_k \eta(b, g_k) < \widehat{\sigma}_0$ — these are 3.4's content (TRAP 2: global-budget leak).
5. Any claim that $\inf_k \widehat{\sigma}_k > 0$ — this is the σ-3 uniform survival, Phase 3's main theorem.
6. Any derivation of "$\widehat{\sigma}_{k+1} > 0$" from a single step — output positivity is structurally provided by the codomain demanding `Valid_{k+1}`, not by S4 alone.

## 6. Label map

| Concept | Formal label (`formal/block-spin-morphism.tex`) | Lean target (`lean/YMGap/RG/BlockSpin.lean`) |
| --- | --- | --- |
| Block-spin configuration map | Definition 2.1 (`def:T-b-config`) | Parameter / instance (abstract) |
| Block-spin polymer map | Definition 2.2 (`def:T-b-poly`) | Parameter / instance (abstract) |
| Site morphism | Definition 2.3 (`def:site-morphism`) | Implicit (uses `Site.Open`, `Site.Morphism` from 2.1) |
| Pushforward on $\mathcal{A}_k$ | Definition 3.1 (`def:pushforward-A`) | (specific implementations defer to 3.x) |
| Pushforward on $\mathcal{S}_k$ | Definition 3.2 (`def:pushforward-S`) | (defers to 3.x) |
| 2-cell $\Theta_k$ | Definition 4.1 (`def:two-cell-theta`) | `BlockSpin.TwoCellTheta` |
| Per-step budget functions | Definition 5.1 (`def:budget-functions`) | Four `V → V → V` parameters in Lean |
| Refined step type | Definition 5.2 (`def:step-type-with-budget`) | `StepTypeWithBudget` |
| Sub-obligations (per milestone) | Definition 6.1 (`def:sub-obligations`) | `Obligation_sf`, `Obligation_lf`, `Obligation_cap`, `Obligation_sigma` |
| Atomic obligation (reconstructed) | Remark 6.3 (`rem:atomic-obligation`) | `StepObligation_decomposed`; `StepObligation` is an alias |
| Sub-witnesses (sorry'd, one per milestone) | (LaTeX states what 3.x must produce; no LaTeX-side sorry) | `step_obligation_sf`, `…_lf`, `…_cap`, `…_sigma` (sorry'd, logged in SORRY_LEDGER `[P2.3-sf]`, `[P2.3-lf]`, `[P2.3-cap]`, `[P2.3-sigma]`) |
| Encoded-but-unverified note (sf ⊥ lf; σ-via-cap-only) | Remark 6.2 (`rem:encoded-unverified`) | Type signatures of `Obligation_lf` (no `sf_part`) and `Obligation_sigma` (only `cap_part`) |

## 7. Pointers

- The formal statements: [`formal/block-spin-morphism.tex`](../formal/block-spin-morphism.tex), compile with `cd formal && latexmk -pdf block-spin-morphism.tex`.
- The Lean formalization: [`lean/YMGap/RG/BlockSpin.lean`](../lean/YMGap/RG/BlockSpin.lean), build with `cd lean && lake build`.
- The Python representation + tests: [`computations/block_spin.py`](../computations/block_spin.py), [`tests/test_block_spin.py`](../tests/test_block_spin.py).
- The diagram of the step and the 2-cell: [`visualizations/structure/block-spin-2cell.tikz`](../visualizations/structure/block-spin-2cell.tikz).
- Motivation: [`docs/context.md`](context.md) §3.3 (the four conditions), §2 (the σ-3 sense).
- Specification: [`docs/outline.md`](outline.md) §10.3–§10.5.
- Open obligations: [`lean/SORRY_LEDGER.md`](../lean/SORRY_LEDGER.md) entry `[P2.3]` (this milestone), inherited `[P2.1]` (parts a and b) surfacing through V2-cap and V3-K of `Valid_{k+1}` in the step's codomain.
