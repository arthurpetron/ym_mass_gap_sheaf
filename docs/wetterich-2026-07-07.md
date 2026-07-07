# The Wetterich (functional-RG) exact-flow mass-term equation: the TRUNCATED (LPA) threshold flow GENERATES + FREEZES a bounded nonzero IR mass (dimensional transmutation, machine-checked); the EXACT flow requires the full non-perturbative `Γ_k''` (the interacting inverse propagator) = singleStep

**Deliverable Lean file:** `lean/YMGap/Continuum/WetterichMassFlow.lean` (wired into `YMGap.lean`).
Full `lake build` **green = 734 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier
types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 14 gated
load-bearing declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}`; no
`sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. MAIN tree, NEW file,
Lean-core only (`Q'`/`Nat` + a decidable `Q'` threshold `if` + the `finSum`/geometric-tail
backbone). Numerics `/tmp/wett_verify.py` (sympy exact + mpmath dps 50). **Committed: nothing**
(per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The Wetterich functional-RG mass-term flow with the THRESHOLD / DECOUPLING structure is
BUILT. The TRUNCATED (local-potential-approximation, LPA) threshold flow is CONSTRUCTIBLE and
GENERATES a bounded nonzero IR mass that FREEZES at the decoupling scale (dimensional
transmutation) — the genuinely new physics beyond the linear `EffectiveActionMassFlow.massFlow`.
The EXACT Wetterich flow's RHS `(Γ_k'' + R_k)^{-1}` requires the FULL non-perturbative inverse
propagator `Γ_k''` (the curvature of the exact effective action = the interacting measure),
which is `singleStep`. So the functional RG does NOT generate the gap constructively for the
real theory — the TRUNCATED threshold flow is a MODEL (generates + freezes a mass), and the
EXACT flow ISOLATES `Γ_k'' = singleStep`. Nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.**

The task's most adversarial branch is **CONFIRMED**: the truncated LPA threshold flow generates
a model mass (constructible); the exact flow requires the non-perturbative `Γ_k''` = the
interacting measure = `singleStep`.

---

## 1. THE MASS-TERM FLOW (task point 1) — projected onto the mass, with the THRESHOLD

The exact Wetterich equation `∂_t Γ_k = (1/2) Tr[(Γ_k''+R_k)^{−1} ∂_t R_k]` (`t = log k`),
projected onto the mass term in the LPA, gives the dimensionless-mass flow

    ∂_t u_k = 2·u_k − c·g²_k·ℓ(u_k) ,     u_k = m²_k/k² ,   ℓ = threshold function.

`ℓ(u)` is `O(1)` while the mode is active (`u < 1`, `m² < k²`) and DECOUPLES (`ℓ → 0`) once the
mode is heavy (`u > 1`, `m² > k²`). Integrated over the blocking `k_n = Λ·b^{−n}` (`b=2`,
`Λ=1`), the physical mass² accumulates the per-shell Wetterich source gated by the sharp
decoupling threshold `Θ`:

    M²_0 = 0  (m²_Λ = 0, perturbatively massless UV);
    M²_{n+1} = M²_n + s_n · Θ(M²_n, k²_n) ,   Θ = 1 if M²_n < k²_n else 0     (`wetterichFlow`)

with `k²_n = (1/4)^n` (`kSq`) and `s_n = c·g²_n·(threshold prefactor)` the shell source. The
**genuinely new piece vs `massFlow`** (a linear always-on recursion) is `Θ` — the DECOUPLING /
FREEZING threshold, the physical mechanism of dimensional transmutation.

## 2. THE THRESHOLD / DECOUPLING (task point 2, the crux) — the flow FREEZES

- **Freezing, PROVED** (`wetterichFlow_freezes`): once the mode is decoupled (`k²_n ≤ M²_n`,
  `u_n ≥ 1`) the threshold `Θ = 0` switches the source off and `M²_{n+1} ≃ M²_n`. The flow STOPS.
  This is the frozen mass = the scale where `m² ~ k²` (dimensional transmutation) — absent from
  a linear flow.
- **Decoupling is REACHED, PROVED** (`wetterichFlow_decoupling_reached`): for the model
  condensate source the dimensionless mass reaches `u_4 ≥ 1` at the FINITE scale `n=4`
  (`k²_4 = 1/256 ≤` the generated mass floor `srcHead = 1/100 ≤ M²_4`), and the mass FREEZES
  (`wetterichFlow_frozen_at_decoupling`: `M²_5 ≃ M²_4`).
- **The frozen mass is bounded, PROVED** (`wetterichFlow_massBounded`): `M²_n ≤ srcSum = 1/70`
  at every scale via `RationalTail.geometric_tail_closure`. With generation
  (`wetterichFlow_massGenerated`, `0 < M²_{n+1}`) the frozen mass sits in `(0, 1/70]`.

Numeric (sympy exact): `M² : 0 → 1/100 → 13/1000 → 139/10000 → 1417/100000`, then FROZEN from
`n=4`; frozen `M² = 1417/100000 ∈ (0, 1/70]`.

## 3. THE DECISIVE CHECK (task point 3) — does the flow generate the gap, or isolate `Γ_k''`?

**Both, split cleanly — the SAME irreducible core, in functional-RG-flow form.**

- The TRUNCATED (LPA) threshold flow is CONSTRUCTIBLE and GENERATES + FREEZES a bounded nonzero
  mass (§1–2), PROVED for the model condensate source `s_n = (1/100)(3/10)^n` — exactly as
  `massFlow` takes its source as given data. This is the genuine new machine-checked piece.
- But this uses the LOCAL truncation of `Γ_k''` and takes the source as GIVEN. The EXACT
  Wetterich RHS `(Γ_k''+R_k)^{−1}` requires the FULL, field-dependent, non-perturbative inverse
  propagator `Γ_k''` (the curvature of the exact effective action = the interacting measure).
- **Adversarial confirmation from the LPA itself:** the LPA flow with a FIXED perturbative `g²`
  has `RHS(u=0) = −c·g² < 0` (verified mpmath) — it does NOT generate a mass by itself; the
  generating source must be the non-perturbative condensate = `Γ_k''` = `singleStep`. So the
  truncation is a model, and the exact non-perturbative input is irreducible.

Encoded (def-alias, UNINHABITED, NOT one of the 5 guarded types):
`ExactWetterichVertex := SingleStepDefectReduction.SingleStepDefectBound`
(`exactWetterichVertex_eq`, `rfl`, Rule 9.8).

## 4. HONEST accounting (task point 4 — refuse dodges)

| object | status | evidence |
|---|---|---|
| Wetterich LPA mass flow `M²_{n+1}=M²_n+s_n·Θ` + sharp decoupling threshold `Θ` | **CONSTRUCTED (new)** | `wetterichFlow`, `activeFac` |
| perturbative flow keeps `M²=0` | **PROVED (axiom-clean)** | `wetterichFlow_perturbatively_massless` |
| condensate source generates `0 < M²`, monotone, `≤ 1/70` | **PROVED for the MODEL source** | `wetterichFlow_massGenerated`, `wetterichFlow_mono`, `wetterichFlow_massBounded` |
| FREEZING: decoupled ⟹ `M²_{n+1} ≃ M²_n` (the Wetterich threshold) | **PROVED (the new decoupling theorem)** | `wetterichFlow_freezes` |
| decoupling reached at finite `n=4`; mass freezes (dimensional transmutation) | **PROVED for the MODEL source** | `wetterichFlow_decoupling_reached`, `wetterichFlow_frozen_at_decoupling` |
| LPA with fixed perturbative `g²` does NOT generate the mass (`RHS(0)<0`) | **VERIFIED (mpmath)** | `wett_verify.py` |
| EXACT flow's non-perturbative `Γ_k''` (interacting inverse propagator) | **OPEN = `singleStep`** | `ExactWetterichVertex = SingleStepDefectBound` (uninhabited) |
| `exp(−x) > 0` / positivity | **TRIVIAL — red herring** | free `Q'` nonnegativity |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types and
produces no unconditional inhabitant of `SingleStepDefectBound`. Guard stays at 5. The
`WetterichVerdict` bundle is inhabited by PROVED facts only (perturbatively massless + generated
+ bounded + decoupling reached + freezes) — NOT a frontier type.

## 5. `#print axioms` (all 14 gated decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
activeFac_nonneg                        : (none)
activeFac_le_one                        : [propext]
wetterichFlow_nonneg                    : [propext]
wetterichFlow_perturbatively_massless   : [propext, Quot.sound]   ← perturbative M²≃0
wetterichFlow_mono                      : [propext]
wetterichFlow_freezes                   : [propext]               ← THE FREEZING (decoupling threshold)
wetterichFlow_le_finSum                 : [propext]
wetterichFlow_massBounded               : [propext]               ← transmutation ceiling M²≤1/70
srcHead_le_flow_one                     : [propext]
wetterichFlow_massGenerated             : [propext]               ← 0 < M² (generation)
wetterichFlow_decoupling_reached        : [propext]               ← u_4 ≥ 1 (finite decoupling)
wetterichFlow_frozen_at_decoupling      : [propext]               ← M²_5 ≃ M²_4 (frozen gap)
exactWetterichVertex_eq                 : [propext, Quot.sound]   ← residual = singleStep
wetterich_verdict                       : [propext, Quot.sound]
```

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (734 jobs).
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring`. All witnesses `Type`-level.
Frontier guard count UNCHANGED at 5.

## 6. HONEST FINAL VERDICT

The Wetterich functional-RG mass-term flow with the threshold/decoupling structure is BUILT.

**CONSTRUCTED (the genuine new pieces):** the Wetterich LPA mass flow
`M²_{n+1} = M²_n + s_n·Θ(M²_n,k²_n)` with the sharp decoupling threshold `Θ` (absent from the
linear `massFlow`); PERTURBATIVE MASSLESSNESS (`s≡0` keeps `M²≃0`, machine-checked); GENERATION
of a strictly positive, monotone, bounded mass from the condensate source; the FREEZING theorem
(decoupled ⟹ the source switches off ⟹ `M²` frozen — the Wetterich threshold); and concrete
DIMENSIONAL TRANSMUTATION (decoupling reached at `n=4`, the mass freezes at `1417/100000 ∈
(0,1/70]`), all PROVED for the model condensate source.

**RESIDUAL (NOT closed):** the truncated (LPA) flow uses the LOCAL truncation and takes the mass
source as GIVEN data; the EXACT Wetterich RHS `(Γ_k''+R_k)^{−1}` requires the FULL
non-perturbative inverse propagator `Γ_k''` = the interacting measure = `ExactWetterichVertex =
SingleStepDefectBound.singleStep` (UNINHABITED). The LPA with a fixed perturbative `g²` provably
fails to generate the mass by itself (`RHS(0) = −c·g² < 0`), confirming the exact `Γ_k''` is
irreducible.

So the functional RG generates the gap only in the TRUNCATED MODEL (a genuine new flow piece +
its freezing/transmutation theorems), and the EXACT flow ISOLATES the non-perturbative
`Γ_k'' = singleStep`. This is a further confirmation of the SAME irreducible core, in
functional-RG-flow form. No guarded frontier bundle is inhabited; nothing is faked; the 4D
Yang–Mills mass gap remains OPEN. The next attack is unchanged: the spacing-uniform gap survival
`singleStep` = the exact non-perturbative `Γ_k''`.
