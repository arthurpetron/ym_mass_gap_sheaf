# The interacting (non-Gaussian) single-polymer measure: the DEFINITE fixed-spacing z₁ is BUILT and PROVED to clear the KP bound; the continuum z₁ (w→1) is isolated = singleStep

**Deliverable Lean file:** `lean/YMGap/Continuum/InteractingSinglePolymerMeasure.lean` (wired into
`YMGap.lean`). Full `lake build` **green = 731 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 11 gated
load-bearing declarations `#print axioms ⊆ {∅, [propext], [propext, Quot.sound]}`; no
`sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. MAIN tree, NEW file,
Lean-core only (`Q'`/`Nat` + the `plaqActivity`/`qpow` backbone). Numerics `/tmp/verify.py`
(mpmath dps 45, sympy exact). **Committed: nothing** (per instruction).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The interacting non-Gaussian single-polymer measure toward z₁ is BUILT at fixed spacing, and —
the genuinely new content — the fixed-spacing z₁ is PROVED to clear the exact KP config-space bound
`z₁ ≤ 1 − w`. But a fixed-spacing z₁ is NOT the continuum z₁: the continuum value (w→1, weak
coupling, a→0) is the renormalon = `singleStep`, isolated as the sole residual.**

Concretely, the GENUINE interacting single-polymer activity is the full su(2) heat-kernel
single-plaquette weight over the EXCITED representations — the NON-Gaussian group integral
`z₁(w) = ⟨1 − ½χ⟩_conn = Σ_{s≥1} dim(s)·w^{C₄(s)}` (`PlaquetteActivity.plaqActivity`), Q'-valued
exactly as `SinglePolymerActivity.z1` demands. NOT the single-mode Gaussian of
`ExactSinglePolymerActivity`, NOT the transcendental one-point surrogate of
`NonpertActivityHeatKernel`. At fixed/strong coupling it is DEFINITE FINITE POSITIVE and clears
`z₁ ≤ 1 − w`; at weak coupling (continuum) it does not, and there is the renormalon.

The task's most adversarial branch is **CONFIRMED**: the interacting measure gives a definite
continuum z₁ only under an assumption that is FALSE for the continuum (all AF scales strong-
coupling); unconditionally it isolates `singleStep`. Nothing is faked; the 4D Yang–Mills mass gap
remains OPEN.

---

## 1. Numeric validation (`/tmp/verify.py`, mpmath dps 45, sympy exact)

- **Exact factorization** `1 − w − 4w³ = (1 − 2w)(2w² + w + 1)` (sympy `factor`); the quadratic
  has discriminant `−7 < 0`, so `2w² + w + 1 > 0` always ⟹ `4w³ ≤ 1 − w` on `[0, 1/2]`, equality
  at `w = 1/2`. (The Lean proof uses the cleaner chain `4w³ ≤ w ≤ 1 − w`, both tight at `1/2`.)
- **`4w³ ≤ 1 − w` on `[0,1/2]`** verified pointwise: `w=0.25 → 0.0625 ≤ 0.75`, `w=0.49 → 0.4706 ≤
  0.51`, `w=0.5 → 0.5 = 0.5`.
- **Exact non-Gaussian activity** `A(w) = Σ_{s≥1}(s+1)w^{s(s+2)}` is a definite finite value:
  `A(0.1)=0.00200003…`, `A(0.3)=0.05419688…`, `A(0.5)=0.26184111…`; all `≤ 4w³ ≤ 1 − w`.
- **Weak coupling fails**: `w=0.9` → `4w³ = 2.916 > 0.1 = 1 − w`; `A(0.9) = 4.179 > 0.1` (the
  character sum has left its radius; the renormalon regime).

---

## 2. What is BUILT / PROVED in Lean-core (all axiom-clean)

### Layer (a) — THE FIXED-SPACING INTERACTING NON-GAUSSIAN z₁ IS A DEFINITE FINITE VALUE

| declaration | content | axioms |
|---|---|---|
| `z1FixedSpacing w M` | the genuine su(2) heat-kernel single-plaquette activity `Σ_{s≥1} dim(s)·w^{C₄(s)}` (= `plaqActivity`) — the NON-Gaussian group integral, Q'-valued | (def) |
| `z1FixedSpacing_nonneg` | `z₁ ≥ 0` (positive-definite value) | propext |
| `z1FixedSpacing_le_cubic` | **DEFINITE FINITE**: `z₁ ≤ 4w³`, uniform in `M`, at strong coupling `0 ≤ w ≤ 1/2` (reuses PROVED `plaqActivity_le`) | propext, Quot.sound |

### Layer (b) — THE GENUINE NON-GAUSSIAN z₁ CLEARS THE KP BOUND (the new content)

| declaration | content | axioms |
|---|---|---|
| `qpow_two_le_quarter` | `w² ≤ 1/4` on `[0,1/2]` (monotonicity) | propext |
| `four_cubic_le_w` | `4w³ ≤ w` on `[0,1/2]` (`w³ = w²·w ≤ (1/4)w`) | propext |
| `w_le_fieldActivity` | `w ≤ 1 − w` on `w ≤ 1/2` (`2w ≤ 1`) | propext |
| **`cubic_le_fieldActivity`** | **`4w³ ≤ 1 − w`** on `[0,1/2]` (new algebraic key, tight at `1/2`) | propext |
| **`z1FixedSpacing_le_fieldActivity`** | **THE KEY CLEARING**: `z₁ ≤ fieldActivity w = 1 − w` at strong coupling — the genuine non-Gaussian activity meets the exact KP config-space bound | propext, Quot.sound |
| `cubic_not_le_fieldActivity_at_weak` | **the weak-coupling refutation**: `4·(9/10)³ > 1 − 9/10` (decide, AXIOM-FREE) — the clearing fails in the continuum tail | (none) |

This is a **strict improvement over `NonpertActivityHeatKernel`**: there the character MOMENT that
cleared the bound was a transcendental one-point *surrogate* (Rule 9.6), and the genuine
strong-coupling polymer activity `e^{−(3/4)t}` *overshot* `g²` at weak coupling. Here the ACTUAL
Q'-valued non-Gaussian activity `Σ_{s≥1} dim(s)·w^{C₄(s)}` clears the exact `z₁ ≤ 1 − w` at strong
coupling — no surrogate, no overshoot.

### Layer (c) — THE INTERACTING MEASURE IS CONSTRUCTIBLE ORDER-BY-ORDER

| declaration | content | axioms |
|---|---|---|
| `interacting_order_by_order_determined` | the non-Gaussian reweighting `e^{−S_int}` truncation against the Isserlis Gaussian base is DETERMINED (`= 3` at order 2) and the free-field dodge `z_n ≡ 0` is REFUTED (reuses `feynTrunc_two_determined`, `isserlis_refutes_free_dodge`) | propext |

### Layer (d) — THE CONDITIONAL PRODUCER + THE CONTINUUM RESIDUAL

| declaration | content | axioms |
|---|---|---|
| `singlePolymerActivity_of_strongCoupling` | CONDITIONAL producer: GIVEN `∀ k, w_{cutoff+k} ≤ 1/2` (all AF scales strong-coupling) it inhabits `SinglePolymerActivity afr`. For the real AF trajectory the hypothesis is FALSE (`w_k → 1`), so it inhabits NOTHING unconditionally — names the sole missing input | (def, open binder) |
| `ContinuumSinglePolymerActivity` | def-alias `:= SingleStepDefectBound` (UNINHABITED) — the continuum z₁ (w→1) = the renormalon = `singleStep` | (def) |
| `continuumSinglePolymerActivity_eq` | the alias is exactly the named residual (rfl, Rule 9.8) | propext, Quot.sound |
| `interacting_z1_verdict : InteractingZ1Verdict` | informational bundle of PROVED facts (nonneg + finite + clears + weak-fails); inhabits NO frontier type | propext, Quot.sound |

---

## 3. THE DECISIVE CHECK — definite continuum z₁, or singleStep?

**Adversarial answer: the interacting measure gives a definite continuum z₁ only under a
continuum-FALSE hypothesis; unconditionally it ISOLATES `singleStep`.**

The `AFRateModulus` trajectory has `w_k → 1` (the continuum a→0 / UV / weak coupling): the
canonical inhabitant is `w_k = 1 − 1/(k+1)`, so `w_0 = 0`, `w_1 = 1/2`, `w_k > 1/2` for `k ≥ 2`.

- The strong-coupling clearing `z₁ ≤ 1 − w` (proved) covers only the coarse scales `w ≤ 1/2`.
- For the continuum tail it FAILS: `cubic_not_le_fieldActivity_at_weak` (`4·(9/10)³ > 1 − 9/10`),
  and the character expansion itself leaves its radius of convergence (`A(0.9) = 4.18 > 1`).
- `singlePolymerActivity_of_strongCoupling` therefore inhabits `SinglePolymerActivity` only
  relative to the (false-for-continuum) hypothesis `∀ k, w_{cutoff+k} ≤ 1/2`. It produces NO
  unconditional inhabitant (open binder), mirroring `singlePolymerActivity_of_gaussianVariance`.

**So the exact non-perturbative input the confined-phase resolution needs** is the value of the
single-polymer activity at `w → 1` (weak coupling) — where the strong-coupling / character-radius
control is gone. This is precisely the spacing-uniform gap survival = `SingleStepDefectBound.
singleStep` = the renormalon, `ContinuumSinglePolymerActivity` (uninhabited). The fixed-spacing z₁
(proved finite) is at `w ≤ 1/2` inside the radius; the continuum z₁ is at `w → 1` outside it — the
residual, exactly as the task's most adversarial branch predicts.

---

## 4. HONEST accounting (refuse dodges)

| object | status | evidence |
|---|---|---|
| fixed-spacing interacting non-Gaussian z₁ = `Σ_{s≥1} dim(s)·w^{C₄(s)}` | **CONSTRUCTED (Q'-valued)** | `z1FixedSpacing` |
| fixed-spacing z₁ positive-definite | **PROVED** | `z1FixedSpacing_nonneg` |
| fixed-spacing z₁ DEFINITE FINITE (`≤ 4w³`, uniform in M) | **PROVED** | `z1FixedSpacing_le_cubic` |
| genuine non-Gaussian z₁ CLEARS `z₁ ≤ 1 − w` at strong coupling | **PROVED (new)** | `z1FixedSpacing_le_fieldActivity`, `cubic_le_fieldActivity` |
| interacting measure determined order-by-order, dodge refuted | **PROVED (reused)** | `interacting_order_by_order_determined` |
| clearing FAILS at weak coupling (continuum tail) | **PROVED (refutation)** | `cubic_not_le_fieldActivity_at_weak` |
| `SinglePolymerActivity` inhabited if ALL AF scales `≤ 1/2` | **CONDITIONAL (false for continuum)** | `singlePolymerActivity_of_strongCoupling` (open binder) |
| CONTINUUM z₁ (w→1) = the renormalon | **OPEN = `singleStep`** | `ContinuumSinglePolymerActivity = SingleStepDefectBound` (uninhabited) |
| `exp>0` / `4w³ ≥ 0` positivity | **TRIVIAL — red herring** | free Q' nonnegativity |

No STOP/cascade condition tripped: the module inhabits none of the 5 guarded frontier types and
produces no unconditional inhabitant of `SinglePolymerActivity` or `SingleStepDefectBound`. Guard
stays at 5. `InteractingZ1Verdict` is inhabited by PROVED facts only — not a frontier type.

---

## 5. `#print axioms` (all 11 gated decls ⊆ {∅, [propext], [propext, Quot.sound]})

```
z1FixedSpacing_nonneg                    : [propext]
z1FixedSpacing_le_cubic                  : [propext, Quot.sound]   ← definite finite
qpow_two_le_quarter                      : [propext]
four_cubic_le_w                          : [propext]
w_le_fieldActivity                       : [propext]
cubic_le_fieldActivity                   : [propext]               ← new: 4w³ ≤ 1−w
z1FixedSpacing_le_fieldActivity          : [propext, Quot.sound]   ← KEY: z₁ ≤ 1−w cleared
cubic_not_le_fieldActivity_at_weak       : (none)                  ← weak-coupling refutation
interacting_order_by_order_determined    : [propext]
continuumSinglePolymerActivity_eq        : [propext, Quot.sound]   ← residual = singleStep
interacting_z1_verdict                   : [propext, Quot.sound]
```

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (731 jobs).
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring` (banned tokens in docstring prose
only). All witnesses `Type`-level. Frontier guard count UNCHANGED at 5.

---

## 6. HONEST FINAL VERDICT

The interacting (non-Gaussian) single-polymer measure toward z₁ is BUILT at fixed spacing: the
genuine su(2) heat-kernel single-plaquette activity `z₁(w) = Σ_{s≥1} dim(s)·w^{C₄(s)}` is a
DEFINITE FINITE POSITIVE Q' value, and — the new content — it CLEARS the exact KP config-space
bound `z₁ ≤ 1 − w` at strong coupling (via the new `4w³ ≤ 1 − w`), a strict improvement over the
transcendental surrogate / weak-coupling overshoot of the prior heat-kernel attempt. The
interacting measure `Gaussian base × e^{−S_int}` is constructible order-by-order (determined,
dodge refuted).

But a fixed-spacing z₁ is NOT the continuum z₁. The AF trajectory has `w_k → 1`; the strong-
coupling clearing covers only the coarse scales and FAILS in the continuum weak-coupling tail. The
sole missing non-perturbative input is the value of the single-polymer activity at `w → 1` — the
renormalon = `ContinuumSinglePolymerActivity = SingleStepDefectBound.singleStep`, UNINHABITED.

No guarded frontier bundle is inhabited; no unconditional inhabitant of `SinglePolymerActivity` or
`SingleStepDefectBound` is produced; nothing is faked; the 4D Yang–Mills mass gap remains OPEN. The
next attack is unchanged: the spacing-uniform gap survival `singleStep` = the continuum z₁ at
`w → 1`.
