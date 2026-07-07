# The Bałaban large-field / small-field control: does suppression beat entropy?

**Deliverable Lean file:** `lean/YMGap/Continuum/BalabanLargeFieldEntropy.lean` (wired into
`YMGap.lean`). Full `lake build` **green = 736 jobs**; `YMGapGuard` **frontier-guard OK = 5**
Clay-frontier types unconditionally uninhabited (UNCHANGED — nothing new inhabited). All 13
gated load-bearing declarations `#print axioms`-clean (`⊆ {∅, [propext], [propext, Quot.sound]}`);
no `sorry`/`sorryAx`, no `native_decide`, no `Classical.*`, no `ring`. Numerics
`/tmp/largefield_verify.py` (mpmath dps 50, sympy exact). **Committed: nothing** (per instruction).
MAIN tree, NEW file, Lean-core only (`Q'`/`CReal`/`Nat` + the `finSum`/`geometric_tail_closure`/
`divPos` backbone).

---

## 0. HEADLINE VERDICT (machine-checked, axiom-clean, maximally adversarial)

The Bałaban large-field control decomposes EXACTLY along the single-scale / multi-scale line:

- **SINGLE MODE / SINGLE SCALE (finite volume) — the suppression BEATS the entropy. CONSTRUCTIBLE
  (PROVED here).** The single-mode Gaussian tail is a bounded geometric sum (finite large-field
  mass), and for any FIXED finite volume `V` a suppression scale `M` with `g²·s·V < M²`
  (`M > g√(s·V)`) is COMPUTED as data — the Gaussian suppression genuinely beats the finite
  entropy.
- **MULTI-SCALE / CONTINUUM (infinite modes) — NO uniform scale beats the entropy. = `singleStep`.**
  For ANY fixed suppression scale `M` a volume `V` with `M² < g²·s·V` is COMPUTED, so the entropy
  across `V → ∞` is UNBOUNDED. The scale-by-scale control (the per-`V` diverging threshold
  `M(V) = g√(s·V)`, the Bałaban RG) is the open `singleStep`.

**So the large-field control gives the measure ONLY at a single scale; the continuum (multi-scale)
control IS the foundational Bałaban RG = `singleStep`.** A single-scale bound is a genuine new
piece, NOT the continuum measure. No frontier bundle inhabited; nothing faked; 4D YM mass gap OPEN.

---

## 1. The math, verified (mpmath dps 50, sympy exact)

**(1) Single-mode Gaussian tail (the suppression).** `∫_M^∞ e^{−φ²/g²} dφ ≤ (g²/2M)·e^{−M²/g²}`
(the standard `∫_M^∞ e^{−ax²} ≤ e^{−aM²}/(2aM)` with `a = 1/g²`). Verified for
`(M,g) ∈ {(1,1),(2,1),(3,½),(5,2)}`: e.g. `M=2,g=1` tail `0.0041455 ≤ 0.0045789`; `M=3,g=½`
tail `9.536·10⁻¹⁸ ≤ 9.665·10⁻¹⁸`. The tail is FINITE and Gaussian-suppressed.

**(2) Suppression vs entropy — the net exponent** `E = M²/g² − s·V`. Suppression beats entropy iff
`M² > g²·s·V`, i.e. `M > M_c = g√(s·V)`. Threshold clean: `g=1,s=½,V=4` ⟹ `M_c = √2 = 1.41421`;
at `M = 1.1·M_c`, `E = +0.42 > 0`; at `M = 0.9·M_c`, `E = −0.38 < 0`.

**(3) Total large-field measure** `~ e^{−M²/g² + V·s}`: `g=1,s=½,V=9` (`M_c = 2.1213`) gives `1.0`
at `M=M_c`, `0.011` at `M=3`, `1.01·10⁻⁵` at `M=4`, `2.1·10⁻¹⁴` at `M=6` — suppressed for `M>M_c`.

**(4) Multi-scale (Archimedean).** Fixed `M=10,g=1,s=½`: entropy wins once `V > 200`. Such `V`
always exists ⟹ no uniform `M` controls all volumes. The continuum entropy is unbounded.

---

## 2. What is PROVED in Lean-core (`BalabanLargeFieldEntropy.lean`, all axiom-clean)

| declaration | content | axioms |
|---|---|---|
| `singleModeSuppression` / `_nonneg` / `_le_one` | the suppression amplitude `e^{−M²/g²}` as a genuine CReal in `[0,1]` (reuses proved `condensateCReal`); positivity TRIVIAL (red herring) | propext, Quot.sound |
| `gaussTailTerm` / **`singleMode_tail_bounded`** | **the single-mode large-field mass is a BOUNDED geometric sum** `Σ_n K·r^n ≤ H = K/(1−r)` (`r<1`, the cell-to-cell Gaussian ratio) — the constructive shadow of `∫_M^∞ e^{−φ²/g²} < ∞` (reuses PROVED `geometric_tail_closure`) | propext |
| `gaussTail_concrete` | concrete non-vacuous instance `Σ_n 1·(½)^n ≤ 2` | propext |
| `entropyScale` / `entropyScale_mono` | the entropy cost `g²·s·V` (scaled by `g²` to compare with `M²`) is NONDECREASING in `V` (more modes ⟹ more entropy) | propext |
| `ofNatGt` / `scaledGt` | the (scaled) Archimedean witness returned as DATA (`Σ'`) | propext, Quot.sound |
| **`suppression_beats_entropy_single_scale`** | **THE DECISIVE SINGLE-SCALE CHECK (data):** `g,s>0`, fixed `V` ⟹ a suppression scale `M` with `entropyScale g s V < suppressionScale M` (`g²·s·V < M²`) is COMPUTED — suppression BEATS finite entropy | propext, Quot.sound |
| **`entropy_beats_fixed_suppression`** | **THE MULTI-SCALE OBSTRUCTION (data):** `g,s>0`, fixed `M` ⟹ a volume `V` with `suppressionScale M < entropyScale g s V` (`M² < g²·s·V`) is COMPUTED — NO uniform `M` controls all volumes | propext, Quot.sound |
| `MultiScaleLargeFieldControl` / `_eq` | def-alias `:= SingleStepDefectBound` (Rule 9.8), UNINHABITED, NOT a guarded frontier type | propext, Quot.sound |
| `largeFieldEntropy_verdict` | informational bundle of the PROVED facts; inhabits NO frontier bundle | propext, Quot.sound |

`nat_le_mul_self` (`n ≤ n²`, axiom-free) is the `Nat` lemma behind `M = ofNat N ⟹ M² ≥ ofNat N`.

---

## 3. THE DECISIVE CHECK — single-scale bound, or the multi-scale RG = `singleStep`?

The two dual theorems ARE the Bałaban dichotomy, machine-checked:

- `suppression_beats_entropy_single_scale` — at a **single scale / finite volume** the entropy
  `g²·s·V` is a FIXED `Q'`, and a large-enough suppression scale `M` (explicitly
  `M = ofNat((g²·s·V).num.toNat + 1)`, so `M² ≥ M > g²·s·V`) beats it. The suppression wins.
  CONSTRUCTIBLE. Together with the finite geometric tail (`singleMode_tail_bounded`) this is the
  genuine single-scale large-field control: the large-field region has small, finite, computable
  measure at fixed volume.
- `entropy_beats_fixed_suppression` — but for the **continuum (infinite modes)** no single `M`
  works: for every fixed `M` there is a `V` (explicitly the scaled Archimedean witness for
  `M²/(g²s)`) with `g²·s·V > M²`. The entropy is unbounded, so the control must supply a
  per-scale, diverging threshold `M(V) = g√(s·V)` — the scale-by-scale Bałaban RG.

Encoded: `MultiScaleLargeFieldControl := SingleStepDefectReduction.SingleStepDefectBound`
(def-alias, UNINHABITED, not one of the 5 guarded frontier types — guard stays at 5, no cascade).

---

## 4. HONEST verdict — does the large-field control give the measure?

**Single-scale: YES, constructibly (the genuine new piece).** The single-mode Gaussian suppression
`e^{−M²/g²}` is a bona-fide CReal in `[0,1]` (positivity the red herring), its large-field tail is
a bounded geometric sum (finite mass), and at any fixed finite volume the suppression provably
beats the (finite) entropy at a computed scale `M > g√(sV)`. These are real theorems about the
concrete `Q'`/`CReal`/`finSum` objects — the free field does NOT subsume them (the geometric-tail
summability and the single-scale threshold are genuine content).

**Multi-scale (continuum): NO — it is `singleStep`.** The entropy across `V → ∞` is unbounded
(`entropy_beats_fixed_suppression`), so no uniform suppression scale controls the continuum. The
scale-by-scale control (the diverging per-scale threshold, the Bałaban RG that beats the entropy
scale-by-scale) is exactly the foundational input `SingleStepDefectBound.singleStep`. A
single-scale bound is a PIECE, not the continuum measure.

**No overclaim.** The large-field control gives the measure only at a single scale; it ISOLATES the
multi-scale Bałaban RG = `singleStep`. This is a further confirmation of the SAME irreducible core
(cf. the config-space `z₁`/renormalon, the instanton large-size IR, the field-space `ρ_phys`),
now in explicit suppression-vs-entropy form, PLUS the genuinely new machine-checked
suppression-beats-finite-entropy and geometric-tail theorems. No guarded frontier bundle is
inhabited; nothing is faked; the 4D Yang–Mills mass gap remains **OPEN**.

---

## 5. Build / guard / axioms (honesty gate)

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
                       uninhabited across YMGap.*
Build completed successfully (736 jobs).
```

`#print axioms` — all 13 gated load-bearing declarations ⊆ `{∅, [propext], [propext, Quot.sound]}`:

```
lt_of_lt_of_le                          : [propext]
ofNatGt                                 : [propext, Quot.sound]
scaledGt                                : [propext, Quot.sound]
singleModeSuppression_nonneg            : [propext, Quot.sound]
singleModeSuppression_le_one            : [propext, Quot.sound]
singleMode_tail_bounded                 : [propext]              ← finite LF mass (geom tail)
gaussTail_concrete                      : [propext]
entropyScale_mono                       : [propext]
nat_le_mul_self                         : (none)
suppression_beats_entropy_single_scale  : [propext, Quot.sound]  ← DECISIVE single-scale
entropy_beats_fixed_suppression         : [propext, Quot.sound]  ← multi-scale obstruction
multiScaleLargeFieldControl_eq          : [propext, Quot.sound]
largeFieldEntropy_verdict               : [propext, Quot.sound]
```

No `Classical.*`, no `sorryAx`, no `native_decide`, no `ring` (banned tokens in docstring prose
only). All witnesses `Type`-level. Frontier guard count UNCHANGED at 5 — nothing new inhabited.

**No STOP condition tripped.** The single-scale large-field suppression BEATS the finite entropy
(CONSTRUCTIBLE, PROVED); the multi-scale continuum control (unbounded entropy, scale-by-scale RG)
is isolated as `singleStep`, not closed. The single open front is the multi-scale Bałaban RG.
