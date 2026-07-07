# Route D — the HIGHER-REP suppression half of `GapChannelDomination`

**Target.** `HeatKernelSecondCumulant.GapChannelDomination` (the convergent residual of
all 3 defect routes) claims the real 4D SU(2) block-spin margin degradation is dominated
by the FUNDAMENTAL-channel (`s = 1`) heat-kernel second cumulant. Two physical halves:

- **large-field / Bałaban half** — small-field vs large-field decomposition (parallel
  agent, `LargeFieldSuppression.lean`);
- **higher-rep half** — the `s ≥ 2` representation channels are negligible vs `s = 1`.

Route D proves the **higher-rep half**, via the PROVED character-tail machinery.

Deliverables: `lean/YMGap/Continuum/RouteDHigherRepTail.lean` (full `lake build` green,
guard OK, axiom-clean), numerics (`numerics.py`, `confirm.py`, mpmath dps 50), this report.

---

## 1. The object and the exact math

Heat-kernel single-plaquette character coefficient of channel `s`:
`dimQ(s)·w^{C₄(s)}`, `dimQ(s)=s+1`, `C₄(s)=s(s+2)` (`C₄(1)=3, C₄(2)=8, C₄(3)=15,…`).
Per-channel second cumulant (in-tree `chanCumulant`):

```
chanCumulant(s,w) = dimQ(s)·( C₄(s)(1−w) − (1 − w^{C₄(s)}) )   (≥ 0 on [0,1]).
```

The **physical channel contribution** to the gap defect carries the heat-kernel weight
`w^{C₄(s)}` (the amplitude for the fluctuation to sit in channel `s`):

```
weightedChan(s,w) := w^{C₄(s)} · chanCumulant(s,w).
```

So the `s ≥ 2` tail carries `w^{C₄(2)} = w⁸`, i.e. `w^{C₄(2)−C₄(1)} = w⁵` smaller than the
`s = 1` term `weightedChan(1,w) = w³·chanCumulant(1,w)`.

**Why the weight is mandatory (adversarial check).** The UN-weighted per-channel cumulant
`chanCumulant(s,w) ~ (s+1)·s(s+2)·(1−w) → ∞` in `s`, so `Σ_{s≥2} chanCumulant(s,w)`
*diverges for every fixed `w<1`* (Object A below, `numerics.py`). The convergent, physical
object is the weighted one `weightedChan`; the weight `w^{C₄(s)}` kills the polynomial
growth. This is the correct reading of "the `s≥2` tail is `O(w^{C₄(2)})=O(w⁸)`".

---

## 2. Numerical validation — the honest regime (mpmath dps 50)

Define the **relative suppression ratio** (Object B — exactly the object proved in Lean):

```
ρ(w) = Σ_{s≥2} weightedChan(s,w)  /  weightedChan(1,w).
```

| `w` | `ρ(w)` | s≥2 dominated by s=1? |
|---|---|---|
| 1/6 ≈ 0.167 (strong-coupling anchor) | 7.3·10⁻⁴ | YES |
| 0.30 | 0.0149 | YES |
| **0.50 (proven Lean threshold)** | **0.2304** | **YES** |
| 0.60 | 0.6750 | YES |
| **0.6377 (true crossover)** | **1.0002** | boundary |
| 0.70 | 1.948 | **NO** |
| 0.90 | 49.44 | **NO** |
| 0.999 | 4.2·10⁷ | **NO** |

**Verdict (adversarial, decisive).** The higher-rep tail is dominated by `s = 1`
**ONLY at strong coupling**: `ρ(w) ≤ 1` for `w ≤ w* = 0.637683…` and **DIVERGES as
`w → 1`** (≈49 at `w=0.9`, ≈4·10⁷ at `w=0.999`). This is the SAME `w→1` blow-up as Route
B's total-second-cumulant refutation — for exactly the same reason (near `w=1` the active
higher-mode count grows and the weight stops suppressing). So the higher-rep half is
**NOT uniform in `w`**; it holds on a strong-coupling window `w ≤ w*` that comfortably
contains the anchor `w = 1/6` (ρ ≈ 7·10⁻⁴).

Object C (pure character tail `Σ_{s≥2}dimQ(s)w^{C₄(s)} / dimQ(1)w³`) crosses 1 at
`w ≈ 0.83`; the cumulant-weighted Object B crosses earlier (0.6377) because the higher-rep
cumulant prefactor `C₄(s)²` amplifies the tail.

---

## 3. What is PROVED in Lean (`RouteDHigherRepTail.lean`, axiom-clean)

Every load-bearing theorem: `#print axioms = [propext, Quot.sound]` only — no
`Classical.*`, no `sorryAx`, no `native_decide`. LEAN-CORE (`Q'`/`CReal`), no Mathlib/ring.

| theorem | statement | axioms |
|---|---|---|
| `weightedChan_le_linEnv` | `weightedChan(s,w) ≤ linEnv(s,w) := w^{C₄(s)}·dimQ(s)·C₄(s)·(1−w)` (linear heat-kernel envelope; from `1−w^{C₄(s)} ≤ C₄(s)(1−w)`, `oneSub_qpow_le`) | propext, Quot.sound |
| **`linEnv_ratio`** | **`linEnv(j+3,w) ≤ (3·w⁷)·linEnv(j+2,w)`** — the character-tail term ratio: successive `s≥2` channels drop by `≤ 3·w⁷` (poly part `dimQ·C₄` grows `≤ 3`, exponent gap `C₄(s+1)−C₄(s)=2s+3 ≥ 7` gives `w⁷`) | propext, Quot.sound |
| `over1_ge` | `2(1−w)² ≤ C₄(1)(1−w) − (1−w³)` (EXACT `renDefect_factor`: `= (1−w)²(2+w) ≥ 2(1−w)²`) | propext, Quot.sound |
| `weightedChan1_ge` | `4·(w³(1−w)²) ≤ weightedChan(1,w)` (fundamental-channel lower bound) | propext, Quot.sound |
| `two_linEnv2_le_gap` | `2·linEnv(2,w) ≤ weightedChan(1,w)` on `[0,1/2]` (strong-coupling comparison, via core `48w⁵ ≤ 4(1−w)`) | propext, Quot.sound |
| **`higherRep_tail_le`** | **`∀ N, Σ_{j<N} weightedChan(j+2,w) ≤ weightedChan(1,w)` on `w ∈ [0,1/2]`** — THE HIGHER-REP SUPPRESSION SUB-LEMMA | propext, Quot.sound |

**Machinery used (PROVED, reused):** `secondOrder_qpow`, `oneSub_qpow_le`, `qpow_add`,
`qpow_antitone` (RGTransport/HeatKernelRGStep); `renDefect_factor` (the exact `s=1`
factorization `3(1−w)−(1−w³) = (1−w)²(2+w)`); **`CharacterTail.geom_series_le`** (the
character-tail geometric closure — the ratio `3w⁷ ≤ 1/2` on `[0,1/2]` closes the series
into `weightedChan(1,w)`).

**Proof architecture of `higherRep_tail_le`.** (i) per-channel `weightedChan ≤ linEnv`;
(ii) `geom_series_le` on `linEnv` with ratio `r = 3w⁷`, head `linEnv(2,w)`, closing value
`H = weightedChan(1,w)`, whose recurrence `linEnv(2,w) + r·H ≤ H` is discharged from
`r ≤ 1/2` (`3w⁷ ≤ 1/2`, `qpow` base-monotone) and `2·linEnv(2,w) ≤ H` (the strong-coupling
comparison); (iii) termwise `Σ weightedChan ≤ Σ linEnv ≤ weightedChan(1,w)`.

The strong-coupling comparison reduces (via the exact `s=1` factorization and the sharp
`s=2` envelope value `24w⁸(1−w)`) to the clean monomial inequality `12w⁵ ≤ 1−w` on
`[0,1/2]` — proven since `12w⁵ ≤ 12(1/2)⁵ = 3/8 ≤ 1/2 ≤ 1−w`. The Lean threshold `w ≤ 1/2`
is a clean rational SUFFICIENT window strictly inside the true crossover `0.6377`.

---

## 4. Honesty ledger — what is reduced, what is NOT claimed

- **`GapChannelDomination` remains UNINHABITED.** Route D does NOT inhabit it, nor
  `SingleStepDefectBound`/`TrueMarginRecursion`. Frontier guard: `5 Clay-frontier types
  unconditionally uninhabited` — GREEN. NO 4D Yang–Mills mass gap is claimed.
- **What is genuinely reduced.** `GapChannelDomination`'s two physical halves are now
  split with the higher-rep half PROVED (as a real theorem about the concrete
  `weightedChan` object): for `w ≤ 1/2`, `Σ_{s≥2} weightedChan(s,w) ≤ weightedChan(1,w)`.
  The residual is the **large-field/Bałaban half** (parallel agent) — exactly the split
  named in the Route B header.
- **Honest regime caveat (Rule 6).** The higher-rep domination is **strong-coupling only**
  (`w ≤ 1/2` proven; true crossover `≈ 0.6377`); it **blows up as `w → 1`**, mirroring
  Route B's total-cumulant refutation. This is reported, not hidden. Along the AF flow
  `w → 1` is the continuum limit, so the higher-rep bound is a strong-coupling anchor
  statement, NOT a continuum-uniform one — the genuinely-hard `w → 1` control stays in the
  large-field/Bałaban residual, not closed here.
- No fake, no free-field, no `δ:=0`. The non-vacuous content is the PROVED §3 theorems
  about the concrete `weightedChan`/`chanCumulant`/`renDefect_factor` objects.

---

## 5. Build / guard / axioms

```
$ lake build
ℹ [681/685] Built YMGap.Continuum.RouteDHigherRepTail (327ms)
✔ [682/685] Built YMGap
ℹ [684/685] Built YMGapGuard
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited
Build completed successfully (685 jobs).
```

`#print axioms` for all 6 load-bearing declarations: `[propext, Quot.sound]` only.

---

## 6. Honest verdict

Route D **PROVES the higher-rep suppression half** of `GapChannelDomination`, constructively
and axiom-clean, via the character-tail geometric machinery: the entire `s ≥ 2`
heat-kernel-weighted second-cumulant tail is dominated by the fundamental (`s=1`) channel
**for the strong-coupling regime `w ≤ 1/2`**. Adversarially, this domination is **NOT
uniform in `w`** — the ratio diverges as `w → 1` (true crossover `0.6377`), the same
blow-up as Route B's total-cumulant refutation, so the continuum-uniform higher-rep control
is NOT established (it belongs to the large-field/Bałaban residual). `GapChannelDomination`
is thereby reduced — via proof, guard-safe — to the LARGE-FIELD half plus this proved
higher-rep bound. The 4D Yang–Mills mass gap remains OPEN; nothing is faked.
