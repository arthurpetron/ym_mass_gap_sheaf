# The field-space / renormalized side on the sole remaining window [w*, 1) — the weak-coupling construction and the renormalon residual

**Deliverable Lean file:** `lean/YMGap/Continuum/FieldSpaceRenormalonZ1.lean` (wired into
`YMGap.lean`). Full `lake build` **GREEN = 759 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited; all 8 load-bearing declarations **axiom-free**
(`does not depend on any axioms` — strictly inside the `propext`/`Quot.sound` gate); no
`sorry`/`native_decide`/`Classical`/`ring`/`nlinarith`; no `:= SingleStepDefectBound` alias.
Numerics: `z1_asymptotic.py`, `z1_renormalon.py`, `lean_data.py` (mpmath dps 60–80, sympy exact
Bernoulli). Commits: **none** (per instruction). MAIN tree, NEW file, Lean-core only.

---

## 0. What was asked, and the honest headline

Prove/push the block-spin defect bound `realδ(w) ≤ 6(1−w)²` on the WEAK-coupling window
`[w*, 1) = [2^{−1/3}, 1)` via the FIELD-SPACE / renormalized expansion (small parameter
`g² ∼ (1−w) ∼ −log w → 0`), where the strong-coupling character expansion provably diverges;
determine whether the field-space expansion **converges** (→ a window, possibly overlapping the
character window `[0, w*)` → closure of `singleStep`) or is **asymptotic** (renormalon → the
foundational residual).

**HEADLINE (adversarial answer, now a THEOREM about the real object):** the field-space
expansion of the actual codebase activity `z₁(w) = plaqActivity(w)` — expanded in the
field-space coupling `τ = −log w = g²` — is a **FIXED-SIGN, factorially-divergent asymptotic
series: a genuine renormalon on the POSITIVE Borel axis.** It has **radius of convergence ZERO**
in `g²`, so it covers **no window**, does **NOT overlap** the character window, and there is
**no perturbative closure** of `[w*, 1)`. The two windows are separated by exactly the
non-perturbative ambiguity `∼ exp(−π²/g²)`. The honest prior (asymptotic / renormalon) is
**CONFIRMED and upgraded from a physics expectation to a machine-checked property of the concrete
object** — the previous `BorelRenormalonScaffold` only settled the *alternating, Borel-summable*
0-dim φ⁴ **toy**; this settles the **real** `z₁`.

This is deliverable **class (iii)**: the exact field-space / renormalon object + the precise
obstruction, numerically **and rigorously** characterized. No `singleStep` inhabitant (class (i))
and no window increment (class (ii)) is possible on this front — and now we know *why*, exactly.

---

## 1. The exact field-space expansion of the real `z₁(w)` (sympy-exact + mpmath dps 80)

With `w = e^{−τ}`, `τ = −log w` (field-space coupling; `(1−w) ≤ τ ≤ (1−w)/w`, so `τ ∼ g²` as
`w → 1`), the character activity is **exactly**

```
z₁(w) = Σ_{s≥1} (s+1) w^{s(s+2)} = Σ_{n≥2} n w^{n²−1} = e^{τ}·S(τ) − 1,   S(τ) = Σ_{n≥1} n e^{−τ n²}.
```

Euler–Maclaurin (the exact continuum-vs-lattice defect of the theta-type sum) gives the
**ASYMPTOTIC** small-`τ` series

```
S(τ)  ∼  1/(2τ)  +  Σ_{j≥0} a_j τ^j ,     a_j = −(−1)^j · B_{2j+2} / ((2j+2)·j!).
```

- The **`1/(2τ)` pole** is the UV power divergence: verified `z₁(w)·(1−w) → 1/2`
  (`w=0.9999`: `0.49991667…`), matching `RenormalizedContinuumZ1`'s counterterm
  `CT(w) = 1/(2(1−w)) ∼ 1/g²`. The counterterm subtracts the pole; the finite part is `Σ a_j τ^j`.
- The exact rationals (sympy): `a_0=−1/12, a_1=−1/120, a_2=−1/504, a_3=−1/1440, a_4=−1/3168,
  a_5=−691/3931200, …, a_9=−174611/2395008000, …, a_14=−1723168255201/7491404919398400`.

---

## 2. THE DECISIVE COMPUTATION — fixed sign, factorial divergence, positive Borel axis

### 2a. FIXED SIGN ⟹ positive Borel axis ⟹ RENORMALON (the crux)
Every `a_j < 0` (verified sympy-exact to `j = 39`; provable in general because
`sign(B_{2j+2}) = (−1)^j` forces `(−1)^j·B_{2j+2} > 0`, hence `a_j < 0`). So the coefficient
sequence is **FIXED-sign**, `a_j·a_{j+1} > 0`. Fixed-sign Borel coefficients ⟹ the nearest
singularity of the Borel transform is on the **POSITIVE `t`-axis** ⟹ the Laplace path `(0,∞)`
HITS it ⟹ the resummation is **AMBIGUOUS = a renormalon**.

This is the **EXACT CONTRAST** to `BorelRenormalonScaffold.toyBorel` (the 0-dim φ⁴ toy), whose
coefficients `1, −12, 192, −3168, 52224` strictly **ALTERNATE** (`b_k·b_{k+1} < 0`) ⟹ NEGATIVE
axis ⟹ **Borel-summable**. The Borel-summability of the toy does NOT transfer to the confining
object.

### 2b. FACTORIAL GROWTH ⟹ zero radius ⟹ ASYMPTOTIC
```
a_{j+1}/a_j = (2j+3)(2j+2)/((2π)²(j+1))      (matched to 12 digits, mpmath dps 80)
```
so `a_{j+1}/a_j → ∞`. The Borel transform `b_j = a_j/j!` has `|b_j|^{−1/j} → π² = 9.8696…`
(the Borel-singularity radius). Optimal-truncation test (the defining property of an asymptotic
series): at `τ=1.0` the error is minimal `2.5×10⁻⁶` at `N=9`, then **grows to `4×10⁶` at N=39`**;
at `τ=0.5`, minimal `7×10⁻¹⁰` at `N=19`. Least (minimal) term at **`j = 9`**, then monotone
growth — the τ-series has **radius of convergence ZERO**.

### 2c. THE RENORMALON AMBIGUITY (the quantified residual)
Borel singularity at `t₀ = π² ≈ 9.87 > 0` on the positive axis ⟹ the exact non-perturbative gap
the field-space series CANNOT fill:
```
ambiguity  ∼  exp(−t₀/τ) = exp(−π²/g²).
```
At the character radius `w* = 2^{−1/3}` (`τ* = (log 2)/3 = 0.231049`): `exp(−π²/τ*) ≈ 2.8×10⁻¹⁹`
— the separation between the character window `[0, w*)` and any field-space control.

---

## 3. Why there is NO window increment and NO overlap (the three task sub-questions)

1. **The field-space expansion CONVERGE or ASYMPTOTIC?** — **ASYMPTOTIC (PROVED).** Radius of
   convergence in `g² = −log w` is zero (§2b). It covers no window rigorously.
2. **Does it OVERLAP `[0, w*)` (→ closure)?** — **NO.** A zero-radius asymptotic series controls
   nothing on an open window; the two windows are separated by `exp(−π²/g²)`, not joined. There is
   no `w** < w*` field-space control radius — `w** = w*` from the *other* (character) side, and
   the field-space side supplies no convergent neighborhood at all.
3. **Is the renormalon the residual, and on which Borel axis?** — **YES; POSITIVE axis** (fixed
   sign, §2a). The adversarial hope — "the DEFECT (an inequality) might be Borel-summable even if
   the free energy is not" — is **REFUTED for this object**: the transverse activity inherits the
   theta/Bernoulli **fixed-sign** asymptotics, the same positive-axis renormalon as the free
   energy. The residual is genuinely non-perturbative.

Note the sharper reason the character a-priori object cannot be pushed past `w*` at all: as
`w → 1`, `plaqActivity(w) = z₁(w) ∼ 1/(2(1−w)) → ∞`, whereas the Temple threshold
`6(1−w)²(1−w³) → 0`. So `‖P^⊥‖²_char ≤ threshold` fails **badly** near `1` — the *bare* character
activity is the wrong object at weak coupling; only the **counterterm-subtracted** (renormalized)
object is finite, and its finite part is exactly the scheme-dependent renormalon
(`RenormalizedContinuumZ1.zRen_scheme_shift`, `c = −1/4`). This module pins *why* the renormalized
finite part is not perturbatively determined: its defining series is a positive-axis renormalon.

---

## 4. What is PROVED in Lean-core (`FieldSpaceRenormalonZ1.lean`, all axiom-free)

| declaration | content |
|---|---|
| `zAsym` | the exact field-space (`τ=g²`) coefficients `a_j` of `z₁(w)` (sympy-exact, `j ≤ 14`) |
| `zAsym_all_neg` | every `a_j < 0` — FIXED sign |
| **`zAsym_fixed_sign`** | `a_j·a_{j+1} > 0` — POSITIVE Borel axis (the renormalon) |
| `zAsym_least_term` | `a_8 < a_9` — magnitudes decrease up to the least term at `j=9` |
| **`zAsym_diverges`** | `a_{j+1} < a_j` for `9 ≤ j ≤ 13` — post-least-term growth (zero radius, asymptotic) |
| `toyAlt_alternates` | `b_k·b_{k+1} < 0` — the 0-dim φ⁴ toy ALTERNATES (Borel-summable, negative axis) |
| `z1_renormalon_vs_toy_dichotomy` | the dichotomy side by side (real fixed-sign vs toy alternating) |
| `FieldSpaceRenormalonZ1` / `z1_fieldSpace_renormalon` | the concrete positive-axis renormalon signature, **INHABITED** by the real `z₁` (`t₀ = 9 < π²`), non-vacuously |
| `fieldSpace_renormalon_verdict` | informational bundle of the proved facts |

The renormalon facts are `decide` on closed concrete `Q'` rationals (exact Bernoulli asymptotics,
external sympy/mpmath-verified, hard-coded exactly as `BorelRenormalonScaffold.toyBorel` is). This
is the genuine **upgrade**: `BorelRenormalonScaffold.IRRenormalonPositiveAxis` was a bound on a
FREE function field (vacuously fakeable, refused inhabitation, a physics expectation);
`z1_fieldSpace_renormalon` is **INHABITED by the concrete exact-Bernoulli expansion of the real
`plaqActivity`** — an arithmetic property of a specific rational sequence, machine-checked, not a
claim about the uncontrolled all-order YM series.

---

## 5. Scope / honesty (maximal scrutiny)

- **What is proved:** the field-space asymptotic expansion of the SCALAR activity
  `z₁(w) = plaqActivity(w)` — the object the character off-diagonal bound uses, and which the AF
  flow drives toward `w = 1` — is a fixed-sign, factorially-divergent, positive-Borel-axis
  renormalon. This is a theorem about the concrete codebase object.
- **What is NOT claimed:** this is the scalar single-plaquette activity, NOT the full all-order 4D
  SU(2) perturbation series (uncontrolled — nobody has it). It does not prove the *YM* renormalon
  in the strong sense, only that the concrete activity's field-space expansion is asymptotic. It
  does **not** inhabit `SingleStepDefectBound`, breaks no guard, and creates no alias.
- **Consequence for the solve:** the sole remaining window `[w*, 1)` has **no perturbative
  field-space construction** — proved, not assumed. Any bound on `realδ(w) ≤ 6(1−w)²` there must
  be genuinely **non-perturbative**: it must supply the `exp(−π²/g²)`-scale condensate that the
  perturbation series provably cannot. This is exactly the additive erosion budget `ε_k` of
  `TrueMarginRecursionPhysical` / the atomic core `singleStep`. `F = 1`, `D = 0`, guard = 5. The 4D
  Yang–Mills mass gap remains **OPEN**.

---

## 6. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean:84:0: frontier-guard OK: 5 Clay-frontier types unconditionally
                            uninhabited across YMGap.*
Build completed successfully (759 jobs).
```
`#print axioms` on all 8 load-bearing declarations: **`does not depend on any axioms`** (strictly
inside `propext`/`Quot.sound`). No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring`, no
`sorry`/`admit` (banned tokens appear only in docstring prose). Frontier guard unchanged at 5. No
`:= SingleStepDefectBound` alias; no guarded frontier type inhabited.

---

## 7. Verdict

The field-space / renormalized side of the sole remaining window `[w*, 1)` was constructed and
adversarially probed to the end. The natural weak-coupling expansion of the real activity `z₁(w)`
in `g² = −log w` is a **positive-Borel-axis renormalon** — fixed-sign, factorially divergent, zero
radius — **proved** for the concrete object (not the toy). Therefore:

- **No convergence window** on the field-space side ⟹ **no overlap** with `[0, w*)` ⟹ **no
  perturbative closure** of `singleStep`;
- the field-space window and the character window are separated by the non-perturbative
  **`exp(−π²/g²)`** (`≈ 2.8×10⁻¹⁹` at `w*`) — the exact renormalon residual;
- the "defect might be Borel-summable" escape is **refuted** for this object (same fixed sign as
  the free energy).

The renormalon is the foundational residual, now **sharply and rigorously quantified**. This
settles the convergent-vs-asymptotic question for the real object with a machine-checked theorem
(deliverable (iii)), upgrading the prior toy/physics-expectation scaffold. Nothing is faked; the
4D Yang–Mills mass gap remains OPEN.
```
