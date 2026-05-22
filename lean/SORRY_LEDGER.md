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
- **obligation**: Given KP certificates `(ρ_sf, K_sf)` for the small-field family and `(ρ_lf, K_lf)` for the large-field family, exhibit a buffer KP certificate `(ρ_∩, K_∩)` with `ρ_∩ = min(ρ_sf, ρ_lf)` and `K_∩ ≤ K_sf + K_lf` such that the regime-specific KP predicate `P` holds at the buffer constants. The constructive content of the obligation is the union-bound estimate `max(a, b) ≤ a + b` applied to the polymer-summability sum (see `formal/sheaf-framework.tex` Proposition 7.1 for the math statement and proof sketch).
- **constructive?**: yes — the statement is Σ-typed (`Σ' c_cap : KPCertificate V P, ...`); the `sorry` isolates only the claim that the regime-specific predicate `P` holds at the explicitly stated buffer constants. The conjectured constants themselves (`min` of decay rates, sum of amplitudes) are baked into the type signature.
- **owed by**: Milestone 3.3 (overlap KP constants).
- **axiom-gate**: `#print axioms domGlue_preserves_KP` reports `depends on axioms: [sorryAx]`. Crucially, **no `Classical.choice`, no `propext`, no `Quot.sound`** — the unique axiom in the dependency closure is `sorryAx`, which is the explicit signal of an unclosed obligation rather than a silent classical lapse.
- **load-bearing status**: this is the actual buffer mechanism. If `max` destroys KP summability, the framework fails at 3.3. Author's heat-kernel/Gaussian conjecture (`formal/sheaf-framework.tex` Remark 7.5): the union-bound estimate is sharp up to a factor `≤ 2` because, for each polymer `X'`, exactly one of `s^sf_X'` or `s^lf_X'` dominates the max — sf for short polymers, lf for long.
- **must not be closed classically**: per AGENTS.md Rule 6, closing this `sorry` later via `Classical.*` would defeat the constructive-law purpose of `lean/`. The closure must come with a constructive predicate `P` from 3.1–3.3 and a constructive proof at those constants.

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
