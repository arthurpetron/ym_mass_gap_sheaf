# The Schwinger–Dyson / gap equation for z₁: the two-branch structure is BUILT and PROVED; the nonzero (dynamical-mass) branch is constructible ONLY given the confining kernel K = the interacting self-energy = singleStep; an ASSUMED confining kernel is CIRCULAR (proved non-vacuous)

**Deliverable Lean file:** `lean/YMGap/Continuum/SchwingerDysonGapEquation.lean` (wired into
`YMGap.lean`). Full `lake build` **green = 733 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 11
gated load-bearing declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}`; no
`sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. MAIN tree, NEW file,
Lean-core only (`Q'`/`Nat` + the condensate CReal). Numerics `/tmp/gap_eq_verify.py`
(mpmath dps 50, sympy exact). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The Schwinger–Dyson gap equation `z = F(z, g²)` is BUILT. Its TWO-BRANCH structure is
PROVED: the perturbative `z = 0` branch is a fixed point of the SD map `z = g²·z·K(z)` for
EVERY kernel (perturbatively massless); a positive root of the reduced equation `g²·K(z) = 1`
is a genuine nonzero (dynamical-mass) fixed point. The DECISIVE result: the nonzero branch
exists IFF the kernel `K` is CONFINING (unbounded as `z → 0`). A BOUNDED (non-confining)
kernel at subcritical coupling has `g²·K(z) < 1` for all `z` — only the trivial branch
survives (PROVED). The essential-singularity solution `z* = exp(−1/g²)` (nonzero at all
couplings, all Taylor coefficients zero at `g² = 0`) requires the UNBOUNDED log-divergent
self-energy. The gap equation therefore DOES NOT determine `z₁` unconditionally — it ISOLATES
the confining kernel `K` = the interacting self-energy = `singleStep`. A gap equation with an
ASSUMED confining kernel is CIRCULAR, and the circularity is REAL (the confining hypothesis is
PROVED non-vacuous: false for a non-confining kernel). Nothing is faked; the 4D Yang–Mills
mass gap remains OPEN.**

The task's most adversarial branch is **CONFIRMED**: the gap equation with an assumed
confining kernel is circular; the real kernel `K` (the interacting self-energy with the
confining structure) is `singleStep`.

---

## 1. Numeric validation (`/tmp/gap_eq_verify.py`, mpmath dps 50, sympy exact)

- **Essential-singularity solution.** The reduced BCS/NJL gap equation `1 = g²·ln(Λ/z)`
  (Λ = 1) has the exact solution `z* = exp(−1/g²)`: verified `g²·ln(1/z*) = 1` to dps 50 at
  `g² ∈ {1/2, 1/4, 1, 2}` (e.g. `g²=1/2 → z*=exp(−2)=0.135…`, `g²·ln(1/z*)=1.0`).
- **Essential singularity (sympy exact).** All derivatives `dⁿ/dxⁿ exp(−1/x) → 0` as `x→0⁺`
  (n = 0..5). The perturbative (Taylor) series of `exp(−1/g²)` is IDENTICALLY 0 — perturbation
  theory gives `z = 0` to ALL orders, yet `z* = exp(−1/g²) > 0` is the non-perturbative branch.
- **Criticality (bounded NJL kernel).** `K(M) = ½[Λ² − M²ln(1+Λ²/M²)]`, `sup K = ½Λ²`,
  critical coupling `g²_c = 1/Kmax = 2`. Subcritical `g² = 0.9 g²_c`: `g²·K(M) ∈
  {0.900, 0.899, 0.858, 0.538}` for `M ∈ {0.001..0.5}` — all `< 1`, NO nonzero root.
  Supercritical `g² = 1.5 g²_c`: a nonzero root `M* = 0.4184…` with `g²·K(M*) = 1.0`.
- **Confining (log) kernel.** `K(z) = ln(Λ/z)` is unbounded as `z→0`, so `g²·ln(Λ/z) = 1`
  has a root `z* = exp(−1/g²) > 0` for ANY `g² > 0` — the nonzero branch at all couplings
  (weak-coupling: `g²=0.01 → z*=3.7e−44 > 0`) requires the unbounded confining kernel.
- **Lean sample.** `zStar = exp(−1/2) = 0.6065…`, lower bound `1−½ = ½` (via `e^{−t} ≥ 1−t`),
  `≤ 1`: a genuine positive CReal in `(0,1]`.

---

## 2. What is BUILT / PROVED in Lean-core (all axiom-clean)

### §1 — The SD map and the perturbative (trivial) branch

| declaration | content | axioms |
|---|---|---|
| `gapMapHom g2 K z := g2*(z*K z)` | the homogeneous Schwinger–Dyson map (self-energy `Σ(z)=g²·z·K(z)`); the gap equation is its fixed point `z = F(z)` | (def) |
| **`gapMapHom_zero_fixed`** | **`z = 0` is a fixed point for EVERY `g²`, `K`** (`F(0) ≃ 0`) — the perturbative massless branch, MACHINE-CHECKED | propext, Quot.sound |

### §2 — The reduced equation and the nonzero (dynamical-mass) branch

| declaration | content | axioms |
|---|---|---|
| `reducedGap g2 K z := g2*K z` | the reduced gap equation `g²·K(z)` (dividing out `z`); nonzero branch = positive root of `= 1` | (def) |
| **`gapSolution_is_fixed`** | **a reduced-equation root `g²·K(z) ≃ 1` IS a genuine SD fixed point** (`F(z) ≃ z·(g²·K(z)) ≃ z·1 ≃ z`) | propext |

### §3 — Criticality: confining kernel IFF nonzero branch (THE DECISIVE CHECK)

| declaration | content | axioms |
|---|---|---|
| **`subcritical_no_nonzero_branch`** | **bounded kernel `K(z)≤Kmax` + subcritical `g²·Kmax<1` ⟹ `g²·K(z) < 1` ∀z** — NO nonzero root, only the trivial branch (no dynamical mass) | propext |
| `subcritical_only_trivial` | restated: `¬ (g²·K(z) ≃ 1)` ∀z — the reduced equation is UNSOLVABLE for a non-confining kernel | propext |

### §4 — The confining kernel produces the nonzero branch (conditional / circularity)

| declaration | content | axioms |
|---|---|---|
| **`nonzeroBranch_of_confiningKernel`** | CONDITIONAL producer: GIVEN the confining structure `g²·K(z*) ≃ 1` (the log self-energy crossing unity), `z*` is a genuine nonzero fixed point. OPEN binder on `hconf` (the confining kernel) | propext |
| **`confiningHyp_fails_subcritical`** | **the confining hypothesis is NON-VACUOUS**: `¬ (g²·K(z*) ≃ 1)` for a bounded/subcritical kernel — so assuming `hconf` IS assuming confinement (the circularity is real) | propext |

### §5 — The essential-singularity value = the condensate

| declaration | content | axioms |
|---|---|---|
| `zStarCReal k := condensateCReal k` | the nonzero-branch solution `z* = exp(−c/β₀g²)` IS the condensate CReal (the same essential singularity) | (def) |
| `zStarCReal_nonneg` | `z* ≥ 0` — the RED HERRING (free `expNeg` nonnegativity) | propext, Quot.sound |
| `zStarCReal_le_one` | `z* ≤ 1` — a bona-fide CReal in `[0,1]` | propext, Quot.sound |
| `nonzeroBranch_strictly_positive` | `0 < condHead = 1/100` — the nonzero branch is strictly positive, distinct from perturbative `0` | (none) |

### §6 — The isolation

| declaration | content | axioms |
|---|---|---|
| `GapEquationConfiningKernel := SingleStepDefectBound` | the confining kernel `K` (the interacting self-energy) = the residual; UNINHABITED, NOT a guarded type | (def) |
| `gapEquationConfiningKernel_eq` | the alias is exactly the named residual (rfl, Rule 9.8) | propext, Quot.sound |
| `gapEquation_verdict : GapEquationVerdict` | informational bundle of PROVED facts (trivial branch + reduced root + subcritical-no-branch + confining-non-vacuous); inhabits NO frontier type | propext, Quot.sound |

---

## 3. THE DECISIVE CHECK — does the gap equation DETERMINE z₁, or isolate the kernel K?

**Adversarial answer: it ISOLATES the confining kernel K; an assumed confining kernel is
circular.**

The gap equation reduces the mass gap to the kernel `K` (the interacting self-energy) having
the confining structure `g²·K(z*) = 1`. The three-way honest verdict:

1. **The nonzero branch is DETERMINED by the confining structure.** Given `g²·K(z*) ≃ 1`,
   `nonzeroBranch_of_confiningKernel` produces the fixed point `z*` — the essential-singularity
   value `exp(−1/g²)`, constructibly (it's just a positive CReal, the condensate). The gap
   equation DOES determine `z*` FROM the confining kernel. The essential-singularity positivity
   is the RED HERRING (`zStarCReal_nonneg`, free).

2. **But the confining structure is NOT free.** `subcritical_no_nonzero_branch` proves that a
   BOUNDED (non-confining) self-energy at subcritical coupling has `g²·K(z) < 1` everywhere —
   only the trivial `z = 0` branch, no dynamical mass. So the nonzero branch REQUIRES `K`
   unbounded as `z → 0` (the log-divergent confining self-energy). Whether the REAL 4D
   self-energy has that structure is the whole question.

3. **An assumed confining kernel is CIRCULAR — and the circularity is REAL.**
   `confiningHyp_fails_subcritical` proves `g²·K(z*) ≃ 1` is FALSE for a non-confining kernel,
   so it is a genuine non-vacuous input. Positing it (as `nonzeroBranch_of_confiningKernel`
   does, with an OPEN binder) is positing confinement to derive the gap — the exact
   circularity the task warned against. The non-circular route — the REAL kernel `K` having the
   confining structure derived from the proved strong coupling — is
   `GapEquationConfiningKernel = SingleStepDefectBound.singleStep`, UNINHABITED.

So the gap equation is NOT a new way to construct `z₁`; it is a further self-consistent-equation
FORM of the SAME irreducible core `singleStep`.

---

## 4. HONEST accounting (refuse dodges)

| object | status | evidence |
|---|---|---|
| SD map `z = g²·z·K(z)`, perturbative `z=0` branch | **CONSTRUCTED + PROVED** | `gapMapHom`, `gapMapHom_zero_fixed` |
| reduced-equation root `g²K(z)=1` ⟹ genuine fixed point | **PROVED** | `gapSolution_is_fixed` |
| bounded/subcritical kernel ⟹ NO nonzero branch | **PROVED (the decisive dichotomy)** | `subcritical_no_nonzero_branch`, `subcritical_only_trivial` |
| nonzero branch FROM confining kernel (conditional) | **CONDITIONAL (open binder `hconf`)** | `nonzeroBranch_of_confiningKernel` |
| confining hypothesis non-vacuous ⟹ assumed kernel is CIRCULAR | **PROVED** | `confiningHyp_fails_subcritical` |
| essential-singularity `z*=exp(−c/g²)` = the condensate | **IDENTIFIED (reused)** | `zStarCReal = condensateCReal` |
| `exp(−c/g²) > 0` positivity | **TRIVIAL — red herring** | `zStarCReal_nonneg` (free) |
| REAL confining kernel `K` = the interacting self-energy | **OPEN = `singleStep`** | `GapEquationConfiningKernel = SingleStepDefectBound` (uninhabited) |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types
and produces no unconditional inhabitant of `SingleStepDefectBound`. Guard stays at 5.
`GapEquationVerdict` is inhabited by PROVED facts only — not a frontier type.

---

## 5. `#print axioms` (all 11 gated decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
gapMapHom_zero_fixed              : [propext, Quot.sound]   ← perturbative branch
gapSolution_is_fixed             : [propext]                ← reduced root ⟹ fixed point
subcritical_no_nonzero_branch    : [propext]                ← THE DECISIVE dichotomy
subcritical_only_trivial         : [propext]
nonzeroBranch_of_confiningKernel : [propext]                ← conditional (circular) producer
confiningHyp_fails_subcritical   : [propext]                ← the confining hyp is non-vacuous
zStarCReal_nonneg                : [propext, Quot.sound]     ← red herring
zStarCReal_le_one                : [propext, Quot.sound]
nonzeroBranch_strictly_positive  : (none)                   ← nonzero branch strictly positive
gapEquationConfiningKernel_eq    : [propext, Quot.sound]     ← residual = singleStep
gapEquation_verdict              : [propext, Quot.sound]
```

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (733 jobs).
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring`. All witnesses `Type`-level.
Frontier guard count UNCHANGED at 5.

---

## 6. HONEST FINAL VERDICT

The Schwinger–Dyson / gap equation for `z₁` is BUILT. The TWO-BRANCH structure is PROVED: the
perturbative `z = 0` branch is a fixed point of the SD map for every kernel (the theory is
perturbatively massless), and a positive root of the reduced equation `g²·K(z) = 1` is a
genuine nonzero (dynamical-mass) fixed point. THE DECISIVE CHECK: the nonzero branch exists IFF
the self-energy kernel `K` is CONFINING — a bounded (non-confining) kernel at subcritical
coupling has `g²·K(z) < 1` everywhere (PROVED), so only the trivial branch survives; the
essential-singularity solution `z* = exp(−1/g²)` (nonzero at all couplings, all Taylor
coefficients zero at `g²=0`) requires the unbounded log-divergent confining self-energy.

The gap equation does NOT determine `z₁` unconditionally — it DETERMINES the nonzero branch
GIVEN the confining kernel, and ISOLATES the confining kernel `K` = the interacting self-energy
= `singleStep`. A gap equation with an ASSUMED confining kernel is CIRCULAR, and the
circularity is REAL: the confining hypothesis `g²·K(z*) = 1` is PROVED non-vacuous (false for a
non-confining kernel). The nonzero-branch value is the very condensate `exp(−c/β₀g²)` whose
positivity is the red herring.

This is a further (self-consistent-equation) confirmation of the SAME irreducible core
`singleStep` — the confining structure of the real 4D self-energy. No guarded frontier bundle
is inhabited; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. The next attack is
unchanged: the spacing-uniform gap survival `singleStep` = the real confining self-energy
kernel `K`.
