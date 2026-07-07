# The interacting, plaquette-COUPLED continuum RG weight (FIELD-SPACE basis) — CONSTRUCT vs BOUND

**Deliverable Lean file:** `lean/YMGap/Continuum/CoupledContinuumWeight.lean` (wired into
`YMGap.lean`; full `lake build` **green = 712 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited). Numerics `verify_coupled.py` (mpmath dps 50,
sympy exact). **Commits: none** (per instruction). MAIN tree, NEW file, Lean-core only
(`Q'`/`Nat`, no Mathlib/`ring`/`native_decide`).

---

## 0. The obligation

Build the field-space coupled-weight scaffold from the proved pieces — the free Gaussian base,
the `g²` single-plaquette vertex, the KP tree domination, the field-space convergence gate — and
decide, with maximal scrutiny, **THE CRUX: does the scaffold CONSTRUCT the interacting coupled
continuum `z_n = ∫ e^{−S_int} χ Dφ / Z`, or only BOUND a free `z_n`?** If it constructs and
cascades to a guarded bundle: STOP + exhaustive audit. If `z_n` stays free: name the exact
foundational gap.

---

## 1. HEADLINE VERDICT (machine-checked, axiom-clean): it BOUNDS. It does NOT CONSTRUCT.

The field-space coupled scaffold assembles cleanly from every proved piece, and it **BOUNDS**
`z_n` (the KP cluster sum converges, `Σ|z_n| ≤ 1/(1−μg²)`). But **it provably does NOT
CONSTRUCT** `z_n`, for two independent, machine-checked reasons. **Nothing closes. No guarded
bundle is inhabited. The free-field dodge is refused. The 4D Yang–Mills mass gap remains OPEN.**

The task's construction path — "the coupled weight = free product × shared-link integrals
(2-body `δ/dim` + Wigner 6j)" — is genuinely constructible **at fixed spacing** (this was already
`ZnCharacterSumFrontier`/`ZnWilsonConstruction`), but it lives in the **character basis, which
provably diverges as `a→0`**. The convergent **field-space basis** carries only an **upper
bound** on `z_n`, not a determination. This module proves that the two facts are irreconcilable
in the present substrate — **the scissors**.

---

## 2. THE TWO MACHINE-CHECKED OBSTRUCTIONS

### (A) `coupled_underdetermined` — the field-space scaffold BOUNDS, it does not CONSTRUCT.

Over the **SAME** free-Gaussian base, the **SAME** `g²` single-plaquette vertex `S`
(`SinglePolymerActivity`, `|z₁| ≤ g²`), the **SAME** connectivity `μ = 6`, and the **SAME** KP
tree domination `|z_n| ≤ μ^n z₁^n`, **two distinct `KPAmplitude` inhabit**:

| inhabitant | `z_n` | KP data (`μ`, `a`) | KP bound `Σ|z_n|≤1/(1−μg²)` |
|---|---|---|---|
| free dodge (`freeKPAmplitude_of_single S`) | `≡ 0` | `(6, z₁)` | identical |
| saturating (`saturatingKP S`) | `μ^n z₁^n` | `(6, z₁)` | identical |

`coupled_same_KP_data` proves the KP data (`.mu`, `.a`) are **literally equal** (`⟨rfl, rfl⟩`), so
`clusterSum_le` gives both the **identical** convergence certificate. Yet
`coupled_underdetermined` proves their amplitudes **differ** wherever the saturating one is
positive (`¬ (dodge.zAmp k n) ≃ (sat.zAmp k n)`, via the constructive apartness `lt_imp_not_eqv`:
`a<b ⟹ ¬ a≃b`). The hypothesis `0 < sat.zAmp k n` is genuinely satisfiable (positive activity ×
connectivity — the non-vacuous case).

**Conclusion:** the scaffold is a **CONTAINER** (an upper bound) the true `z_n` lives in, not a
**CONSTRUCTION** of it. Every ingredient the task lists leaves `z_n` underdetermined. Excluding
the free dodge needs a genuine **LOWER determination** — the actual integral — which the library
lacks.

### (B) `library_base_fails_wick` — the library's base measure is NOT a true Gaussian.

Constructing `z_n = ∫ e^{−S_int} χ Dφ / Z` means expanding `e^{−S_int}` and integrating the
interaction monomials against the Gaussian reference via **Wick/Isserlis contractions**. The
library's minimal base measure (the mean-zero two-point law on `{+s,−s}`,
`SinglePolymerGaussian.gaussSecondMoment`) reproduces the **second** moment `⟨A²⟩ = s²`
(`library_base_matches_variance`, `rfl`) — which is exactly why it can **BOUND** (`z₁ ≤ g²`) —
but its **fourth** moment is

    ⟨A⁴⟩_library = s⁴     versus     ⟨A⁴⟩_Gaussian = 3⟨A²⟩² = 3s⁴  (Isserlis).

`library_base_fails_wick` (kernel-`decide`, **AXIOM-FREE**): `gaussFourthMoment 1 = 1 < 3 =
wickFourthMoment 1`. The normalized kurtosis of the library measure is `1`, not the Gaussian `3`
(sympy exact, `verify_coupled.py`). **The base measure fails Wick's theorem at the first
nontrivial order:** it can variance-match (BOUND) but cannot perform the Isserlis contraction that
CONSTRUCTING the interacting amplitudes requires.

---

## 3. THE SCISSORS (`scissors`, machine-checked, axiom-free)

    (character blade)  coeffW(9/10) 1 = 2·(9/10)³ = 729/500 > 1   — constructible basis DIVERGES at a→0
    (field    blade)  gaussFourthMoment 1 = 1 < 3 = wickFourthMoment 1 — convergent basis FAILS Wick (BOUND only)

The coupling is **constructible only in the character/6j basis, which diverges** throughout the
continuum window `w ∈ (0.794, 1)` (crossover `2w³=1` at `w* = 0.79370…`, verified dps 50).
Convergence holds **only in the field-space basis** (`μ(1−w) < 1`), whose amplitude is
**underdetermined** (A) and whose base measure **fails Wick** (B). **No single object of this
library carries both** the shared-link coupling and a convergent, Wick-correct continuum measure.

---

## 4. Cascade / STOP audit (MANDATORY — this is the mass gap)

**No STOP condition tripped. No guarded bundle inhabited. No cascade triggered. No new fakeable
frontier bundle created.**

- The module proves theorems ABOUT the field-space coupled scaffold (bounding-not-constructing,
  Wick failure, scissors). It does **NOT** inhabit `InteractingContinuumMeasure`,
  `FieldMeasureSubstrate`, `KPAmplitude`'s `treeDom` genuinely, `IsserlisPenroseData.pertRep`, or
  any of the 5 guarded Clay-frontier types (`Tier0Scorecard`, `UniformSpacingFloor`, `ClayTarget`,
  `ClayTargetPinned`, `FrontierDAG`). Full build: `frontier-guard OK: 5 … unconditionally
  uninhabited`, **712 jobs** (711 → 712 = the +1 module).
- **Deliberately did NOT create a new "uninhabited frontier" structure for the coupled integral.**
  Any `Q'`/`CReal`-level structure for `z_n = ∫e^{−S_int}χ/Z` is either **fakeable** (inhabited by
  a surrogate — the free dodge, or `wickMoment := 3⟨A²⟩²` with a saturating `zAmp`) or requires
  **baking a contradiction** (fake uninhabitedness) — both Rule-9 violations. The honest finding:
  **the coupled integral cannot even be STATED as a determining equation in the present
  vocabulary**; that inexpressibility IS the substrate gap. It is already NAMED, as far as the
  vocabulary allows, by `InteractingContinuumMeasure.uniformWickTreeDom` and
  `FieldMeasureSubstrate.wickTreeDom` — this module proves WHY they stay open (one-sided bounds an
  interaction-free dodge satisfies).
- The free-field dodge is **refused**: `coupled_dodge_zero` (`zAmp ≡ 0`) +
  `freeContinuum_no_interaction` (connected 2-point vanishes) exhibit it as the interaction-free
  Gaussian free field, which the scaffold cannot itself exclude.

**`#print axioms`** for all 10 load-bearing decls ∈ {∅, `[propext]`, `[propext, Quot.sound]`}. The
decisive facts (`library_base_fails_wick`, `coupledFixedWeight_char_diverges_continuum`,
`scissors`, `wickFourthMoment_eq`, `library_base_matches_variance`) are **axiom-free**. No
`Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`/`admit` (banned tokens appear only in
docstring prose).

---

## 5. Numeric validation (`verify_coupled.py`, mpmath dps 50, sympy exact)

1. **Wick failure:** two-point law `⟨A⁴⟩ = s⁴`, Gaussian `3s⁴`; ratio `3`; normalized kurtosis
   `1 ≠ 3`; at `s=1`, `1 < 3`.
2. **Character divergence:** `2w³ = 0.25, 1.0000, 1.458, 1.941, 1.994` at
   `w = 0.5, 0.794, 0.9, 0.99, 0.999`; crossover `w* = 0.7937005259840997…`; `2·(9/10)³ = 729/500 > 1`.
3. **Field-space convergence:** `μ(1−w) = 0.6, 0.06, 0.006 < 1` at `w = 0.9, 0.99, 0.999`.
4. **BOUND-not-CONSTRUCT:** at `w=0.99`, KP bound `1/(1−μg²) = 1.0638…`; dodge `Σz_n = 0`,
   saturating `Σz_n = 0.06383…` — **both satisfy the identical bound, amplitudes distinct.**

---

## 6. HONEST FINAL VERDICT

The interacting, plaquette-coupled continuum RG weight in the field-space basis is **assembled
from every proved piece** — but the assembly **BOUNDS `z_n`, it does NOT CONSTRUCT it**
(`coupled_underdetermined`: same base/vertex/connectivity/tree-domination/convergence-bound, yet
the amplitude is underdetermined — the free dodge and the saturating amplitude both inhabit). The
library's base measure **fails Wick/Isserlis at 4th order** (`library_base_fails_wick`,
`⟨A⁴⟩ = s⁴ ≠ 3s⁴`), so it can only variance-match, never perform the contraction that constructing
the coupled amplitudes requires. The **scissors** (`scissors`): the coupling is constructible only
in the character basis (which diverges at `a→0`); convergence holds only in the field-space basis
(whose amplitude is underdetermined and whose base fails Wick).

**THE EXACT FOUNDATIONAL GAP** is the coupled infinite-dimensional Gaussian field integral
`z_n = ∫ e^{−S_int} χ Dφ / Z`, requiring (i) a genuine infinite-dimensional Gaussian base measure
obeying Wick/Isserlis (the library's finite two-point law FAILS this) and (ii) the coupled
interaction integrated against it with the partition ratio, **DETERMINING** (not merely bounding)
each connected amplitude. This is the constructive-QFT substrate the character-basis `Q'`/`CReal`
library **fundamentally lacks** — the coupled integral cannot even be stated as a determining
equation in the present vocabulary.

**The interacting continuum measure is NOT constructible from the proved pieces; it is the genuine
foundational substrate the library lacks — located exactly, not closed. No guarded frontier bundle
is inhabited; the free-field dodge is refused; nothing is faked; the 4D Yang–Mills mass gap remains
OPEN.**

---

## 7. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (712 jobs).
```

`CoupledContinuumWeight.lean`, 10 load-bearing decls, `#print axioms ∈ {∅, [propext],
[propext, Quot.sound]}`. Lean-core only; reuses PROVED `gaussSecondMoment`,
`freeKPAmplitude_of_single`, `kpAmplitude_of_singlePolymer`, `clusterSum_le`,
`charRate_exceeds_one_at_continuum`, `zCharCluster_nonneg`, `freeContinuum_no_interaction`. All
witnesses `Type`-level.
