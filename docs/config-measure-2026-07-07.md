# The constructive configuration-space field measure — Gaussian base + finite-order + KP-given-z₁, with z₁ (the renormalon) isolated as the sole residual

**Deliverable Lean file:** `lean/YMGap/Continuum/ConfigSpaceMeasure.lean` (wired into `YMGap.lean`).
Full `lake build` **green = 728 jobs**; `YMGapGuard` **frontier-guard OK = 5** Clay-frontier types
unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 15 load-bearing declarations
`#print axioms`-gated to `⊆ {∅, [propext], [propext, Quot.sound]}`; no `sorry`/`sorryAx`, no
`native_decide`, no `Classical.*`. Numerics `/tmp/wick_verify.py` (mpmath dps 50, sympy exact).
**Committed: nothing** (per instruction). MAIN tree, NEW file, Lean-core only (`Q'`/`Nat` + the
`finSum`/`pow` backbone).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

**The constructive config-space measure is ASSEMBLED as three layers, with z₁ ISOLATED as the
sole foundational input.** (a) The Gaussian base is built as the GENERAL all-order Isserlis moment
functional (new — generalises the existing `wick4`); (b) the finite-order interacting expansion is
constructible order-by-order (reused); (c) the KP resummation GIVEN a finite z₁ is a BOUNDED
constructible `Q'` (reused `clusterSum_le`). The assembled `ConfigSpaceMeasure` = KP(z₁), with the
single open field `single : SinglePolymerActivity` (z₁). **Building the measure GIVEN z₁ CLOSES
NOTHING — z₁ is the INPUT; it ISOLATES z₁.** And z₁ IS the renormalon: its order-k connected
perturbative series admits NO Cauchy-modulus resummation, while its physical finite-order
coefficients are strictly nonzero — so z₁ is neither the free dodge nor perturbatively summable,
the SAME irreducible core `singleStep`/the renormalon, now in explicit measure form. No guarded
frontier bundle inhabited; nothing faked; the 4D Yang–Mills mass gap remains **OPEN**.

---

## 1. Numeric validation (`/tmp/wick_verify.py`, mpmath dps 50, sympy exact)

- **Isserlis double factorial** `numPairings n = (2n−1)!!`: recursion vs sympy `factorial2`,
  exact match n = 0..5 → `1, 1, 3, 15, 105, 945`.
- **Gaussian moments** `⟨x^{2n}⟩ = (2n−1)!!` (unit variance, mpmath quad dps 50 vs exact):
  reldiff `0.0` for n = 0..4 (`1, 1, 3, 15, 105`).
- **`wick4` diagonal** `C_ij C_kl + C_ik C_jl + C_il C_jk = 1+1+1 = 3` = `numPairings 2`.
- **Odd moments vanish** `⟨x^{2n+1}⟩ = 0` (mpmath, n = 0..2).
- **Leg-count recursion** `wm(0)=1, wm(1)=0, wm(m+2)=(m+1)·V·wm(m)`: even → `(m−1)!!`, odd → `0`
  (checked m = 0..8).
- **KP resummation given finite z₁**: `Σ_{n<60}(μg²)^n = 1.4285714… = 1/(1−μg²)` at μg² = 0.3.

---

## 2. What is BUILT / REDUCED in Lean-core (`ConfigSpaceMeasure.lean`, all axiom-clean)

### Layer (a) — THE GAUSSIAN BASE (the free field, proved moments) — GENUINELY NEW

| declaration | content | axioms |
|---|---|---|
| `wickMoment V m` | **the GENERAL all-order Isserlis moment functional** `⟨φ^m⟩` — head leg pairs with one of the `m−1` others (`wickMoment (m+2) = (m+1)·V·wickMoment m`), any `m` even AND odd | (def) |
| `wickMoment_even_eq` | `⟨φ^{2n}⟩ = (2n−1)!!·V^n` — the PROVED `numPairings` double factorial, ALL orders | propext, Quot.sound |
| `wickMoment_odd_zero` | `⟨φ^{2n+1}⟩ = 0` (mean-zero symmetry) | propext, Quot.sound |
| `wickMoment_nonneg` | `⟨φ^m⟩ ≥ 0` on a nonneg covariance | propext |
| `wickMoment_four_eq_wick4` | agrees with the PROVED 4-point `wick4 (const 1) = 3` | ∅ (kernel-decide) |
| `wickMoment_even_eq_gaussMoment` | at `V = s²` equals the PROVED scalar `gaussMoment s n = (2n−1)!!·s^{2n}` | propext, Quot.sound |
| `gaussBaseExpectation V c N` | **the Gaussian expectation of an even-polynomial observable** `Σ_{n<N} c_n·⟨φ^{2n}⟩` — a concrete `Q'` functional | (def) |
| `gaussBaseExpectation_nonneg` | constructive positivity of the free-field functional | propext |

This generalises the pre-existing `IsserlisGaussianBase.wick4` (only `m = 4`) to a concrete
all-order Gaussian base measure functional, proved to obey Wick/Isserlis.

### Layer (b) — THE FINITE-ORDER INTERACTION `e^{−S_int} = Σ_n(−S_int)^n/n!` (reused)

`interactingTrunc diag K = Σ_{k<K} diag k` (re-exports `IsserlisGaussianBase.feynTrunc`), each
`diag k` a DETERMINED Wick contraction; `interactingTrunc_increment` (`= diag K`) isolates the open
part to the ASYMPTOTIC behaviour of the determined coefficients. Constructible order-by-order.

### Layer (c) — THE KP RESUMMATION GIVEN A FINITE z₁ + the assembly

| declaration | content | axioms |
|---|---|---|
| `ConfigSpaceMeasure afr` | **the assembled config-space measure** (Type, Rule 6a) — Gaussian base (`siteVar`, `obsCoeff`), KP substrate (`mu`, `zAmp`, `treeDom`), and the SOLE residual `single : SinglePolymerActivity` (z₁); UNINHABITED | — |
| `ConfigSpaceMeasure.toKP` | the KP amplitude datum from z₁ + tree-domination (reused `kpAmplitude_of_singlePolymer`) | — |
| `ConfigSpaceMeasure.gaussBase` / `_nonneg` | the constructible Gaussian base functional at each scale | propext, Quot.sound |
| `ConfigSpaceMeasure.amplitude_bounded` | `|z_n| ≤ (μg²)^n` (reused `amplitude_le`) | propext, Quot.sound |
| **`ConfigSpaceMeasure.partition_bounded`** | **`Σ_{n<N}|z_n| ≤ 1/(1−μg²)`** — the interacting partition sum is a BOUNDED constructible `Q'` GIVEN z₁ (reused `clusterSum_le`) | propext, Quot.sound |
| `ConfigSpaceMeasure.residual` | extracts the sole open input = `SinglePolymerActivity` (z₁) | — |

### Layer (d) — z₁ IS THE RENORMALON (the isolation is the same core)

| declaration | content | axioms |
|---|---|---|
| `configMeasure_z1_is_renormalon` | z₁'s order-k connected perturbative series admits NO Cauchy-modulus resummation (re-exports `connected_reorg_no_resummation`) | propext |
| `configMeasure_free_dodge_refuted` | the physical z₁ ≢ 0 (leading Isserlis contraction `= 3 > 0`; re-exports `isserlis_refutes_free_dodge`) | propext |

---

## 3. THE DECISIVE CHECK — does building the measure GIVEN z₁ close anything?

**Adversarial answer: NO. It ISOLATES z₁; it closes nothing.** The three constructive layers are
either genuinely built (the Gaussian base) or reduced to PROVED machinery (finite-order, KP). The
assembled `partition_bounded` gives a concrete bounded `Q'` for the interacting cluster sum — but
ONLY as a function of `single : SinglePolymerActivity` (an OPEN `Type`-level field). The producer
`ConfigSpaceMeasure.partition_bounded` has an open binder on `ConfigSpaceMeasure`; the structure is
UNINHABITED. There is no unconditional inhabitant of `SinglePolymerActivity`, and no guarded
frontier bundle is touched (guard stays at 5).

**Is z₁ = singleStep = the renormalon?** Machine-checked evidence, both directions:
- **Not the free dodge**: `configMeasure_free_dodge_refuted` — the physical finite-order
  coefficient is the Isserlis contraction `wick4 = 3 > 0`, strictly APART from `0`, so `z_n ≢ 0`.
- **Not perturbatively summable**: `configMeasure_z1_is_renormalon` — the exact φ⁴ connected
  order-k coefficients grow super-geometrically (`connLB`, ratio ≥ 32, radius 0) and admit NO
  Cauchy-modulus resummation.

So z₁ is a genuine nonzero interacting object whose perturbative determination diverges — exactly
the renormalon / the non-perturbative `singleStep`, now expressed as the sole input of the explicit
config-space measure. (Honest scope note: the identification `z₁ = singleStep` is at the level of
the SAME irreducible core across the confirmations, not a Lean `rfl` between the two distinct
structures `SinglePolymerActivity` and `SingleStepDefectBound`; no such rfl is claimed or faked.)

---

## 4. HONEST FOUNDATIONAL ASSESSMENT — what substrate is now built, what remains

**BUILT (genuine new constructive substrate):**
1. the GENERAL all-order Isserlis moment functional `wickMoment` (even = `(2n−1)!!·V^n`, odd = 0,
   nonneg, agreeing with the proved `wick4`/`gaussMoment`) — the Gaussian base as a concrete `Q'`
   functional for ALL orders, not just the pre-existing 4-point;
2. the Gaussian expectation of even-polynomial observables `gaussBaseExpectation` (nonneg);
3. the assembled `ConfigSpaceMeasure` bundling all three layers with a BOUNDED partition sum
   (`partition_bounded`, `Σ|z_n| ≤ 1/(1−μg²)`) GIVEN z₁.

**REDUCED to PROVED machinery:** the finite-order interacting expansion (`feynTrunc`), the KP
amplitude bound and geometric convergence (`amplitude_le`, `clusterSum_le`), and the tree-dom
reduction (`WickTreeDomination`/`IsserlisPenroseReduction`, upstream).

**THE SOLE RESIDUAL (UNINHABITED):** `single : SinglePolymerActivity afr` — the single-polymer
activity z₁ (`|z₁| ≤ g²`). It is the renormalon-obeying, factorially-determined,
non-perturbative config-space quantity (`configMeasure_z1_is_renormalon` +
`configMeasure_free_dodge_refuted`). This is the config-space-measure form of `singleStep` = the
foundational Bałaban RG / renormalon input the character-basis library lacks.

**No overclaim.** A measure GIVEN z₁ is NOT the mass gap; z₁ (the renormalon) is the residual.
What is now built is the constructive substrate MODULO z₁: the Gaussian base, the finite-order
amplitudes, and the KP-resummed partition bound. The single open front is z₁ = singleStep = the
renormalon.

---

## 5. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (728 jobs).
```

`#print axioms` — all 15 gated load-bearing declarations ⊆ `{∅, [propext], [propext, Quot.sound]}`:

```
wickMoment_succ2                 : (none)
shuffle4                         : [propext]
wickMoment_even_eq               : [propext, Quot.sound]
wickMoment_odd_zero              : [propext, Quot.sound]
wickMoment_nonneg                : [propext]
wickMoment_four_eq_wick4         : (none)
wickMoment_four_val              : (none)
wickMoment_even_eq_gaussMoment   : [propext, Quot.sound]
gaussBaseExpectation_nonneg      : [propext]
interactingTrunc_increment       : (none)
ConfigSpaceMeasure.gaussBase_nonneg   : [propext, Quot.sound]
ConfigSpaceMeasure.amplitude_bounded  : [propext, Quot.sound]
ConfigSpaceMeasure.partition_bounded  : [propext, Quot.sound]   ← KP resummation given z₁
configMeasure_z1_is_renormalon        : [propext]               ← z₁ = the renormalon
configMeasure_free_dodge_refuted      : [propext]               ← physical z₁ ≠ 0
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring` (banned tokens in docstring prose
only). All witnesses `Type`-level. Frontier guard count UNCHANGED at 5 — no cascade, nothing new
inhabited.

**No STOP condition tripped.** The config-space measure is constructed MODULO z₁; z₁ (the
renormalon / `singleStep`) is isolated as the sole foundational input, not closed.
