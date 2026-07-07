# The non-perturbative (entire heat-kernel) test of the single-cluster activity `z_1`

**Deliverable Lean file:** `lean/YMGap/Continuum/NonpertActivityHeatKernel.lean` (wired into
`YMGap.lean`; full `lake build` **green = 715 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Numerics `nonpert_numerics.py` (mpmath dps 50,
sympy exact). Commits: **none** (per instruction). MAIN tree, NEW file, Lean-core only
(`Q'`/`CReal`, no Mathlib/`ring`/`native_decide`; axiom gate propext/Quot.sound only).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**R1 does NOT close from the entire heat kernel. `SinglePolymerActivity` is NOT inhabited. No
cascade to any guarded bundle. The 4D Yang–Mills mass gap remains OPEN.**

The library's single-plaquette Wilson functional `coeffW(t,s) = dim(s)·e^{−t·C₂(s)}` **is genuinely
ENTIRE in `t`** — the non-perturbatively resummed single plaquette, with NO factorial/Borel problem
**at fixed spacing**. That part of the task's premise is CORRECT and is now formalized. But the
decisive test is negative: the entire heat kernel supplies **two distinct scalars that sit on
opposite sides of the required bound `z_1 ≤ g²`**, and **neither is the connected field-space
activity the KP obligation demands**. The one that clears the bound is a transcendental *surrogate*
(the one-point moment); the one that is a genuine polymer activity *overshoots* exactly where KP
needs it (weak coupling). The residual survives, sharpened.

---

## 1. The setup (SU(2), the library's genuine object)

- `WilsonFunctional.wilsonCharExp t s = dim(s)·e^{−t·C₂(s)}`, `C₂(s)=s(s+2)/4`, `dim(s)=s+1`.
- Fundamental `s=1`: `C₂(½)=3/4`, `dim=2` ⟹ `coeffW(t,fund) = 2·e^{−(3/4)t}`.
- **Average plaquette** `⟨½χ_{1/2}⟩_t = e^{−(3/4)t}` — the entire, non-perturbative factor
  (`avgPlaq` in Lean; `wilsonCharExp_fund` proves `wilsonCharExp t 1 = 2·avgPlaq`, definitionally —
  it IS the library's object, not a fresh model).
- `t = g²`. `w = e^{−t}`, `fieldActivity(w) = 1 − w`. KP needs `z_1(w_k) ≤ fieldActivity = 1 − w_k`
  (`KPFieldAmplitude.SinglePolymerActivity.z1_le_g2`); the task's stated (looser) target is
  `z_1 ≤ g² = −log w`.

**Entire (no Borel at fixed spacing).** `1 − e^{−(3/4)t}` has Taylor coefficients (sympy, exact)
`3/4, −9/32, 9/128, −27/2048, …` — decaying, radius of convergence ∞. Every fixed-spacing connected
amplitude is a finite combination of `e^{−t·C₂(r)}`, hence entire in `t`. The factorial/Dyson
radius-0 growth is a property of the **weak-coupling PERTURBATIVE `g²`-expansion** of these entire
quantities (the `a→0` continuum), not of the fixed-spacing quantities themselves.

---

## 2. The DECISIVE dichotomy (numerics: mpmath dps 50; all exact facts sympy-verified)

The entire heat kernel gives two scalars, on OPPOSITE sides of `z_1 ≤ g²`:

| candidate `z_1` | value | `≤ g² = t`? | `≤ fieldActivity = 1−w`? | what it is |
|---|---|---|---|---|
| **character MOMENT** `1 − e^{−(3/4)t}` | `(3/4)g² + O(g⁴)` | **YES**, worst ratio → **3/4** (0 viol. over `t∈(0,10]`) | **YES** (0 viol., `moment−fieldact < 0` throughout) | one-point correlation `⟨1−½χ_p⟩` — a **surrogate**, transcendental |
| **strong-coupling POLYMER** `e^{−(3/4)t}` | `1 − (3/4)g² + …` | **NO** for `t < 0.6255` (all of weak coupling) | — | a genuine polymer activity, small only at STRONG coupling |
| field-space Gaussian `1−e^{−t}(1−2t)` (`g²=4t`) | `(3/4)g² + O(g⁴)` | YES (`ExactSinglePolymerActivity`) | proved only `≤ g²`, **NOT** `≤ 1−w` | leading field-space fluctuation — the object KP actually wants |

Key exact facts (sympy):
- The character moment and the field-space Gaussian **agree at leading order `(3/4)g²`** (the
  fundamental Casimir) but **DIFFER at `O(g⁴)`**: `char − field = 5g⁶/96 − g⁴/8 ≠ 0`. They are
  **not the same object**; the character moment is not the connected activity.
- The strong-coupling polymer activity `e^{−(3/4)t}` crosses `g²=t` at `t = 0.6255…`; below that
  (all of weak coupling) it exceeds `g²`. Rigorous lower bound: `e^{−(3/4)t} ≥ 1 − (3/4)t > t` for
  `t < 4/7 = 0.5714…`.

**Why the "moment clears the bound" is NOT a closure.** `⟨1−½χ_p⟩ = z_1 + Σ_{n≥2}(alternating
connected clusters)`; it equals the connected Ursell `z_1` only at leading order. So it is a
Rule 9(6) **surrogate**, not the connected activity — and it is transcendental, so it cannot be the
`Q'`-valued `z1` that `SinglePolymerActivity` requires. The genuine polymer activity in this basis
(`e^{−(3/4)t}`) is `≈ 1` at weak coupling, failing `≤ g²` precisely where KP's small-activity gate
`μg² < 1` lives.

---

## 3. What is PROVED in Lean-core (`NonpertActivityHeatKernel.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `wilsonCharExp_fund` | `coeffW(t,fund) = 2·avgPlaq` (the entire library object; rfl) | propext, Quot.sound |
| `avgPlaq_geRat_zero` | the entire factor `e^{−(3/4)t}` is a finite `CReal`, `≥ 0` (no Borel) | propext, Quot.sound |
| `charMomentActivity_geRat_zero` | `1 − e^{−(3/4)t} ≥ 0` | propext, Quot.sound |
| **`charMoment_le_g2`** | **the character MOMENT activity `1 − e^{−(3/4)t} ≤ g² = t`** (Casimir margin `3/4`, via transcendental `oneSub_le_expNeg`) | propext, Quot.sound |
| `avgPlaq_geRat_oneSub` | alternating lower bound `e^{−(3/4)t} ≥ 1 − (3/4)t` | propext, Quot.sound |
| **`strongPolymer_not_le_g2`** | **THE REFUTATION**: `¬ (e^{−(3/4)t} ≤ g²)` at weak coupling `t=1/10` (activity `≥ 37/40`, over 9× the bound) | propext, Quot.sound |

No `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit` (checked). All witnesses
`Type`-level. The refutation is fully formal: `avgPlaq_geRat_oneSub` + the `leRat` upper bound with
slack `ε=1/100` would force `37/40 ≤ 12/100`, refuted by `decide`.

---

## 4. Answering the task's four rigor points

1. **Is `coeffW` entire (single-plaquette non-perturbatively fine)?** YES — proved/used
   (`avgPlaq`, `wilsonCharExp_fund`; Taylor radius ∞). The single plaquette has no Borel problem.
2. **The interacting single-cluster `z_1` — character `4w³`/overshoot vs field-space `(3/4)g²`?**
   Determined exactly. The character single-plaquette **moment** `1−e^{−(3/4)t}` has leading
   `(3/4)g²` and clears the bound; the character **polymer activity** `e^{−(3/4)t}` overshoots at
   weak coupling; the field-space Gaussian `(3/4)g²` clears `≤ g²` but not `≤ 1−w`. The three
   agree only at the leading Casimir `(3/4)g²` and diverge beyond (exact `O(g⁴)` split above).
3. **Does the interacting `z_1` satisfy `z_1 ≤ g²` WITHOUT the Borel problem (coeffW entire)?**
   The FIXED-SPACING interacting amplitude is entire (no Borel) — but the specific object that
   clears `z_1 ≤ g²` (the moment) is a transcendental SURROGATE, not the connected `Q'` activity;
   the genuine connected/polymer activity does NOT clear the weak-coupling bound. So `z_1 ≤ g²`
   is NOT constructed for the right object. `SinglePolymerActivity` NOT inhabited.
4. **Is the Borel problem fixed-spacing or only `a→0`?** **Only `a→0`.** At fixed spacing every
   object is entire (finite `Σ e^{−t·C₂}`), no factorial. The Borel/Dyson factorial is the
   weak-coupling perturbative `g²`-expansion (the continuum). Consistent with Osterwalder–Seiler /
   convergent strong-coupling polymer expansion.

---

## 5. Cascade / STOP audit (mandatory — this is the mass gap)

**No STOP condition tripped. No guarded bundle inhabited. No cascade.**

- The module proves theorems ABOUT the entire heat-kernel activity; it inhabits NONE of the 5
  guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
  `ClayTargetPinned`, `FrontierDAG`). It produces NO unconditional inhabitant of
  `KPFieldAmplitude.SinglePolymerActivity`, `KPAmplitude`, or `InteractingContinuumMeasure`.
- `charMoment_le_g2` bounds the transcendental one-point moment (a surrogate), which is NOT the
  `Q'`-valued connected `z1`; `strongPolymer_not_le_g2` REFUTES the genuine polymer activity route.
  So there is nothing to STOP on — the closure attempt is refuted at the named seam.
- Full build: `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited`, **715 jobs**
  (714 → 715 = the +1 module). `#print axioms` for all 6 load-bearing decls ⊆ `{propext, Quot.sound}`.

---

## 6. HONEST FINAL VERDICT

The entire Wilson heat-kernel `coeffW = dim·e^{−t·C₂}` is a real, non-perturbative object with **no
Borel problem at fixed spacing** — this is proved and it is the correct, important half of the
task's premise. But it does **not** deliver the Kotecký–Preiss single-polymer activity `z_1 ≤ 1−w`:

- the character MOMENT `1−e^{−(3/4)t}` clears `z_1 ≤ g²` with the Casimir margin `3/4`, but is the
  one-point correlation function (a surrogate agreeing with the connected `z_1` only at leading
  order) and is transcendental — it does not legitimately inhabit `SinglePolymerActivity`;
- the character POLYMER activity `e^{−(3/4)t}` is a genuine activity but **overshoots `g²`
  throughout weak coupling** (`strongPolymer_not_le_g2`), exactly where KP's gate `μg²<1` operates.

**R1's activity is NOT constructible from the entire heat kernel.** The genuine residual is
sharpened: the weak-coupling **connected field-space activity `z_1 ≤ 1−w`** for the real non-Gaussian
su(2)/Wilson theory (the transcendental Gaussian model gives only `≤ g²`, `ExactSinglePolymerActivity`),
together with the `a→0` continuum (R2) where the Borel/Dyson factorial actually lives. Nothing is
faked; no guarded frontier bundle is inhabited; the 4D Yang–Mills mass gap remains OPEN.
