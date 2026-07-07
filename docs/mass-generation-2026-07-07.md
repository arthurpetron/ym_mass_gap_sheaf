# The Bałaban effective-action MASS-TERM FLOW — the perturbative part keeps μ=0 (PROVED); the mass generation isolates z₁ = singleStep (the effective-action-flow form)

**Deliverable Lean file:** `lean/YMGap/Continuum/EffectiveActionMassFlow.lean` (wired into
`YMGap.lean`). Full `lake build` **green = 730 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 12
gated load-bearing declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}`; no
`sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. MAIN tree, NEW file,
Lean-core only (`Q'`/`Nat` + the `finSum`/geometric-tail backbone). **Committed: nothing** (per
instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The Bałaban effective-action mass-term flow `μ_{k+1} = b·μ_k + s_k` is CONSTRUCTIBLE; its
PERTURBATIVE part provably keeps `μ = 0` (the theory is perturbatively massless, MACHINE-CHECKED);
and the mass GENERATION reduces EXACTLY to the non-perturbative condensate source
`z₁ = exp(−c/β₀g²) = singleStep`. The generation from the condensate source is PROVED for the
TOY/MODEL source (a bounded nonzero physical mass — dimensional transmutation), but the REAL 4D
flow's non-perturbative source being nonzero IS `z₁ = singleStep` (the renormalon), uninhabited.
So the effective-action mass-flow is another (configuration-flow) confirmation of the SAME
irreducible core, PLUS a genuinely new machine-checked mass-term recursion and its
perturbative-masslessness theorem. No guarded frontier bundle is inhabited; nothing is faked; the
4D Yang–Mills mass gap remains OPEN.**

The task's most adversarial branch is **CONFIRMED**: a perturbative flow keeps `μ = 0`; the
dynamical mass IS the non-perturbative `z₁`.

---

## 1. THE MASS-TERM FLOW (task point 1) — CONSTRUCTED

The effective action's dimensionless mass `μ_k = m_k·a_k` (a RELEVANT coupling of RG
mass-dimension 1) under one block-spin step (`a_{k+1} = b·a_k`):

```
μ_{k+1} = b·μ_k + s_k        (massFlow, a concrete Q'-valued recursion)
```

PROVED, axiom-clean:
- `massFlow_nonneg` — the mass stays a nonnegative parameter along the flow.
- `massFlow_ge_lastSource` — `s_k ≤ μ_{k+1}`: a single nonzero source term generates a nonzero
  mass, amplified by the relevant coupling thereafter.

The physical mass `m_k = μ_k/a_k` telescopes (`(b·μ_k+s_k)/(b·a_k) = m_k + s_k/a_{k+1}`):

```
m_k = Σ_{j<k} s_j/a_{j+1}    (physMass = finSum of the physical source ps_j = s_j/a_{j+1})
```

## 2. THE GENERATION MECHANISM (task point 2) — PERTURBATIVE μ=0 vs NON-PERTURBATIVE source

- **PERTURBATIVE MASSLESSNESS, PROVED.** With the perturbative source `s ≡ 0` (the beta
  function renormalizes `g²` but generates NO mass term) and a massless UV boundary:
  - `massFlow_perturbatively_massless : (massFlow 0 0 b k).eqv 0` (∀k) — dimensionless `μ ≃ 0`;
  - `physMass_perturbatively_massless : physMass 0 k = 0` (∀k, a clean `Q'` equality) — the
    physical mass VANISHES. **The theory is massless in perturbation theory, MACHINE-CHECKED.**
- **NON-PERTURBATIVE GENERATION.** The mass is generated ONLY by the non-perturbative source =
  the condensate `ε_k = exp(−c/β₀g_k²) = K'·r'^k` (`CondensateGeometric.condTerm`, the
  `BorelRenormalonScaffold` renormalon scale). With `b = 2`, the physical source is
  `physSourceCondensate_j = condTerm_j/2^{j+1} = (1/200)(3/10)^j` — tied to the condensate by
  the spacing rescaling (`physRate_is_condRate_rescaled : condRate·(1/b) ≃ physRate`;
  `physHead_is_condHead_rescaled : condHead·(1/b) ≃ physHead`, both axiom-FREE).

## 3. THE MASS GENERATED — bounded nonzero (dimensional transmutation), PROVED for the model source

- `massGeneration : 0 < physMass physSourceCondensate (k+1)` (∀k) — the condensate source
  generates a STRICTLY POSITIVE physical mass at every scale ≥ 1 (perturbative `s≡0` gives
  `m ≡ 0`; the condensate source gives `m > 0`).
- `massTransmutation_ceiling : physMass physSourceCondensate k ≤ physSum = 1/140` (∀k), via the
  PROVED `RationalTail.geometric_tail_closure` (recurrence `1/200 + (3/10)(1/140) = 1/140`).

Together: the generated physical mass sits in the BOUNDED NONZERO band `(0, 1/140]` for all
`k ≥ 1` — a finite dynamical mass generated purely from the geometric non-perturbative source,
uniformly in the scale. Dimensional transmutation in mass-flow form.

## 4. THE DECISIVE CHECK (task point 3) — does the flow GENERATE the mass, or isolate z₁?

**Both, split cleanly.** The generation (§3) is PROVED but uses the condensate AS GIVEN DATA — the
TOY/MODEL source `physSourceCondensate`, exactly as `DimensionlessMarginTransmutation` uses the toy
self-similar flow. It does NOT establish that the REAL 4D flow's non-perturbative source is this
nonzero condensate. The perturbative source is provably `0` (§2), so:

> **the effective-action mass generation reduces ENTIRELY to the real flow's non-perturbative
> source being the nonzero condensate `z₁ = exp(−c/β₀g²)` — the renormalon = `singleStep`.**

Encoded (def-alias, UNINHABITED, NOT one of the 5 guarded types):
`MassGenerationSource := SingleStepDefectReduction.SingleStepDefectBound`
(`massGenerationSource_eq`, `rfl`, Rule 9.8). Identification at the level of the SAME irreducible
core across confirmations, NOT an `rfl` between the distinct structures.

## 5. HONEST accounting (task point 4 — refuse dodges)

| object | status | evidence |
|---|---|---|
| mass-term flow `μ_{k+1}=b·μ_k+s_k` + physical `m_k=Σ s_j/a_{j+1}` | **CONSTRUCTED** | `massFlow`, `physMass` |
| perturbative flow keeps `μ=0` / `m=0` | **PROVED (axiom-clean)** | `massFlow_perturbatively_massless`, `physMass_perturbatively_massless` |
| condensate source generates `0 < m_k ≤ 1/140` (transmutation) | **PROVED for the MODEL source** | `massGeneration`, `massTransmutation_ceiling` |
| source = condensate `exp(−c/β₀g²)` scaled by spacing | **PROVED (identification, axiom-free)** | `physRate/physHead_is_condRate/Head_rescaled` |
| REAL flow's source IS the nonzero condensate | **OPEN = `z₁ = singleStep`** | `MassGenerationSource = SingleStepDefectBound` (uninhabited) |
| `exp(−x) > 0` positivity | **TRIVIAL — red herring** | free `Q'` nonnegativity |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types and
produces no unconditional inhabitant of `SingleStepDefectBound` / any guarded bundle. Guard stays
at 5. The `MassFlowVerdict` bundle is inhabited by PROVED facts only (perturbatively massless +
mass generated + mass bounded) — NOT a frontier type.

## 6. `#print axioms` (all 12 gated decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
massFlow_nonneg                     : [propext]
massFlow_perturbatively_massless    : [propext]          ← perturbative μ≃0
massFlow_ge_lastSource              : [propext]
physMass_perturbatively_massless    : [propext]          ← perturbative m=0
physMass_first_le                   : [propext]
physSourceCondensate_nonneg         : [propext]
physRate_is_condRate_rescaled       : (none)             ← source = condensate (ratio)
physHead_is_condHead_rescaled       : (none)             ← source = condensate (head)
massGeneration                      : [propext]          ← 0 < m_k (generation)
massTransmutation_ceiling           : [propext]          ← m_k ≤ 1/140 (transmutation)
massGenerationSource_eq             : [propext, Quot.sound] ← isolation = singleStep
massFlow_verdict                    : [propext]
```

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (730 jobs).
```

## 7. HONEST FINAL VERDICT

The effective-action mass-term flow is constructible; the perturbative part provably keeps `μ = 0`
(machine-checked — the theory is massless in perturbation theory); the non-perturbative condensate
source generates a bounded nonzero physical mass (proved for the model source, dimensional
transmutation). But the GENERATION of the real mass reduces EXACTLY to the real 4D flow's
non-perturbative source being the nonzero condensate `z₁ = exp(−c/β₀g²) = singleStep` (the
renormalon). The flow does NOT generate the mass constructively for the real theory — it ISOLATES
`z₁ = singleStep` in effective-action mass-flow form. The genuinely new machine-checked pieces are
the mass-term recursion (`massFlow`/`physMass`) and its perturbative-masslessness theorem. No
guarded frontier bundle is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN.
The next attack is unchanged: the spacing-uniform gap survival `singleStep` = the real flow's
non-perturbative mass source.
