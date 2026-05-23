# Sorry Ledger

This ledger lists every `sorry` in the Lean formalization, per
`AGENTS.md` Rule 6.

Every `sorry` in `lean/` must appear here with:

- **milestone** — which `work_plan.md` milestone the obligation belongs to,
- **file** — `lean/YMGap/.../foo.lean`,
- **theorem / def name**,
- **obligation** — what the `sorry` stands for, in one sentence,
- **constructive or propositional** — whether discharging the obligation requires producing a witness (constructive) or only a propositional truth.

A `sorry` standing for a **constructive** obligation must never be closed later by a classical proof without explicit sign-off recorded in this ledger.

## Entries

### [P2.1] overlap summability preservation, owed by 3.3

- **milestone**: 2.1 (work_plan.md L184–202)
- **file**: `lean/YMGap/Sheaf/Gluing.lean`
- **decl**: `YMGap.Sheaf.domGlue_preserves_KP`
- **obligation (load-bearing, two parts)**:

  **(a) Existence of P at the conjectured constants.** Given KP certificates `(ρ_sf, K_sf)` for the small-field family and `(ρ_lf, K_lf)` for the large-field family, exhibit a buffer KP certificate `(ρ_∩, K_∩)` with `ρ_∩ = min(ρ_sf, ρ_lf)` and `K_∩ ≤ K_sf + K_lf` such that the regime-specific KP predicate `P` holds at the buffer constants. The constructive content is the union-bound estimate `max(a, b) ≤ a + b` applied to the polymer-summability sum (see `formal/sheaf-framework.tex` Proposition 7.1 for the math statement and proof sketch). The Σ-typed Lean signature pins this obligation; the `sorry` is its analytic discharge.

  **(b) Tightness of the union bound.** Beyond *existence* of a buffer KP datum, Milestone 3.3 must also verify that the additive estimate `K_∩ ≤ K_sf + K_lf` is *tight enough* — i.e. the factor-2 union bound does not hide a fat band of buffer polymers for which neither `s^sf` nor `s^lf` is the true max, in which case the additive bound is genuinely lossy rather than worst-case-of-2 lossy. This is the substance of `formal/sheaf-framework.tex` Conjecture 7.4 (`conj:gaussian-sharpness`), explicitly flagged there as a conjecture and not a proved fact: the sf and lf bounds live in different units (`|X'|_phys / a_k` vs `|X'|_plaq`), and whether they admit a clean polymer-by-polymer crossover or a fat lossy band is exactly the original §3.1 unit-mismatch difficulty, settleable only against concrete activity forms.

  Part (a) without part (b) gives the framework a *true* statement that is potentially *useless*: a buffer KP certificate exists, but its $K_\cap$ might be too large to feed the inductive step. Closing the Lean `sorry` ultimately requires both. Part (b) is not captured in the current Lean type signature (which only asserts `K_∩ ≤ K_sf + K_lf`, not tightness); a tightness statement would be a separate downstream theorem, naturally introduced in Milestone 3.3 against concrete activity forms.

- **constructive?**: yes for (a) — the Σ-typed signature exhibits the constants and isolates only the predicate-holds claim; for (b), the obligation is intrinsically against concrete polymer activities and will be a constructive estimate once 3.1, 3.2 produce them.
- **owed by**: Milestone 3.3 (overlap KP constants), with 1.3 / 1.4 providing the concrete activity forms that make (b) verifiable.
- **axiom-gate**: `#print axioms domGlue_preserves_KP` reports `depends on axioms: [sorryAx]`. Crucially, **no `Classical.choice`, no `propext`, no `Quot.sound`** — the unique axiom in the dependency closure is `sorryAx`, the explicit signal of an unclosed obligation rather than a silent classical lapse.
- **must not be closed classically**: per AGENTS.md Rule 6, closing this `sorry` later via `Classical.*` would defeat the constructive-law purpose of `lean/`. Closure of (a) must come with a constructive predicate `P` from 3.1–3.3 and a constructive proof at those constants; (b) must come with a constructive tightness estimate.

### [P2.3] block-spin step inhabitation — SUPERSEDED by [P2.3-addendum]

> **Status update (P2.3-addendum):** This atomic entry is superseded by the four per-milestone sub-obligations below. The single `step_obligation_witness` is now an assembly of the four sub-witnesses; it inherits `sorryAx` precisely while any sub-witness remains open. Discharging the atomic obligation reduces to closing the four children. The entry below is preserved for the original phrasing; the binding obligations are the children.

### [P2.3-addendum] decomposition of [P2.3] into four sub-obligations

- **milestone**: 2.3-addendum (commit `[P2.3-addendum]`)
- **file**: `lean/YMGap/RG/BlockSpin.lean` (refactored), `formal/block-spin-morphism.tex` §6 (Definition 6.1, Remark 6.2 encoded-but-unverified)
- **what changed**: The atomic `StepObligation` of P2.3 has been decomposed into four typed sub-obligations: `Obligation_sf`, `Obligation_lf`, `Obligation_cap` (takes `sf_part`, `lf_part`), `Obligation_sigma` (takes `cap_part` only). The atomic form is recovered as `StepObligation_decomposed`. Coupling structure is exposed at the type level.
- **encoded-but-unverified structural predictions** (the entire point of the addendum being on record):
  - `Obligation_lf` takes no `sf_part` input — sf ⊥ lf is encoded, **unverified**. Confirmed when 3.2 closes against this signature; refuted otherwise.
  - `Obligation_sigma` takes only `cap_part` (not direct `sf_part`/`lf_part`) — η via cap-only is encoded, **unverified**. Confirmed when 3.4 closes against this signature; refuted otherwise.
  - These predictions are self-correcting: if they are wrong, the corresponding milestones cannot close at the current types, and the signatures will need additional coupling edges. The audit point is exactly when each closes.

### [P2.3-sf] small-field budget obligation, owed by 3.1

- **milestone**: 2.3-addendum child / 3.1 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_sf`
- **obligation**: Choose `eps_sf : V → V → V` and produce, for every `Valid` input `s_k`, a `c_sf_next : KPCertificate V P` satisfying `s_k.c_sf.rho - eps_sf b s_k.g ≤ c_sf_next.rho` (S1).
- **constructive?**: yes — Σ'-typed; the rho-budget is a constructive inequality.
- **owed by**: Milestone 3.1.
- **axiom-gate**: `[sorryAx]` only.
- **must not be closed classically**: per AGENTS.md Rule 6.

### [P2.3-lf] large-field budget obligation, owed by 3.2

- **milestone**: 2.3-addendum child / 3.2 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_lf`
- **obligation**: Choose `eps_lf : V → V → V` and produce, for every `Valid` input `s_k`, a `c_lf_next : KPCertificate V P` satisfying `s_k.c_lf.rho - eps_lf b s_k.g ≤ c_lf_next.rho` (S2).
- **constructive?**: yes.
- **owed by**: Milestone 3.2.
- **axiom-gate**: `[sorryAx]` only.
- **structural prediction encoded**: this obligation takes no `sf_part` input. See `[P2.3-addendum]` for the prediction's status.
- **must not be closed classically**: per AGENTS.md Rule 6.

### [P2.3-cap] overlap budget obligation, owed by 3.3

- **milestone**: 2.3-addendum child / 3.3 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_cap`
- **obligation**: Given closed `sf_part : Obligation_sf` and `lf_part : Obligation_lf`, choose `delta_cap : V → V → V` and produce `c_cap_next` satisfying S3 plus the buffer-glue invariants at scale `k+1` (V3-ρ: `c_cap_next.rho = min sf_step.rho lf_step.rho`; V3-K: `c_cap_next.K ≤ sf_step.K + lf_step.K`).
- **constructive?**: yes.
- **owed by**: Milestone 3.3.
- **axiom-gate**: `[sorryAx]` only. (Once closed, the result will inherit `[P2.1]` part (a) `domGlue_preserves_KP` `sorryAx` and Conjecture 7.4 tightness obligation through V2-cap/V3-K of the constructed certificate.)
- **must not be closed classically**: per AGENTS.md Rule 6.

### [P2.3-sigma] σ̂-transport budget obligation, owed by 3.4

- **milestone**: 2.3-addendum child / 3.4 closes
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_sigma`
- **obligation**: Given closed `sf_part`, `lf_part`, `cap_part`, choose `eta : V → V → V` and produce `sigmaHat_next : V` satisfying S4 (`s_k.sigmaHat - eta b s_k.g ≤ sigmaHat_next`) and V1 (`0 < sigmaHat_next`).
- **constructive?**: yes (per-step part).
- **owed by**: Milestone 3.4 (per-step). The **global** budget closure `Σ_k η(b, g_k) < σ̂_0` is a separate downstream claim about an infinite sum's convergence — NOT this entry. See `lean/YMGap/Constructive/Rationals.lean` (Milestone 3.0) docstring for the boundary of the ℚ-only representation w.r.t. infinite sums; whether ℚ-bounds suffice for the sum's convergence is a question to be re-examined at 3.4 specifically.
- **axiom-gate**: `[sorryAx]` only.
- **structural prediction encoded**: this obligation takes only `cap_part`, not direct `sf_part`/`lf_part`. See `[P2.3-addendum]` for the prediction's status.
- **must not be closed classically**: per AGENTS.md Rule 6.

### [P2.3] (original) block-spin step inhabitation, owed by 3.1–3.4

- **milestone**: 2.3 (work_plan.md L237–260)
- **file**: `lean/YMGap/RG/BlockSpin.lean`
- **decl**: `YMGap.RG.step_obligation_witness`
- **obligation**: Exhibit a term of type `StepObligation V P PolyAtlas b` — that is, choose budget functions `(eps_sf, eps_lf, delta_cap, eta) : V → V → V` and produce a step function inhabiting `StepTypeWithBudget V P PolyAtlas b eps_sf eps_lf delta_cap eta`, satisfying the four per-step conditions S1–S4 of `docs/context.md` §3.3 / `formal/block-spin-morphism.tex` Definition 5.2.
- **constructive?**: yes — the obligation type is Σ'-typed (the budget functions and the step function are data); the proofs of S1–S4 are constructive inequalities; the codomain demands `Valid s_next`, a constructive predicate.
- **owed by (joint)**:
  - Milestone 3.1 (`eps_sf` + sf-certificate pushforward),
  - Milestone 3.2 (`eps_lf` + lf-certificate pushforward),
  - Milestone 3.3 (`delta_cap` + buffer-certificate pushforward; inherits 2.1's `domGlue_preserves_KP` sorry through V2-cap and Conjecture 7.4 tightness through V3-K),
  - Milestone 3.4 (`eta` + S4 / Θ_k transport).
- **axiom-gate**: `#print axioms step_obligation_witness` reports `depends on axioms: [sorryAx]`. Crucially, **no `Classical.choice`, no `propext`, no `Quot.sound`**. The unique axiom in the dependency closure is `sorryAx`, the explicit signal of an unclosed constructive obligation rather than a silent classical lapse.
- **per-step scope**: the obligation is single-step. No conjunct mentions `Σ_k`, no clause asserts a uniform-in-`k` property. The global budget closure (`Σ_k η < σ̂_0`, `Σ_k Δ_∩ < ∞`, `inf_k σ̂_k > 0`) is Milestone 3.4's separate downstream content — Phase-3 territory, never a 2.3-level claim. Closure of this `[P2.3]` sorry must respect that boundary.
- **must not be closed classically**: per AGENTS.md Rule 6. Closure requires constructive budget functions from 3.1–3.4 and a constructive step term against them.

## How to add an entry

```markdown
### [P1.x] short title

- **milestone**: 1.x (work_plan.md)
- **file**: `lean/YMGap/.../foo.lean`
- **decl**: `theorem foo`
- **obligation**: <one sentence>
- **constructive?**: yes / no
- **notes**: <free text>
```
