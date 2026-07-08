# A-priori bound on the per-scale transverse off-diagonal ‖P_k^⊥‖ — construction increment

**Front (a), sharpest scalar target.** Lean: `lean/YMGap/Continuum/OffDiagonalActivityBound.lean`
(imported into `YMGap.lean`). Full `lake build` GREEN (757 jobs), guard OK (5 frontier types
uninhabited), axiom-clean `[propext, Quot.sound]`. No `native_decide`, no `ring`/`nlinarith`,
no `sorry`. `decide` only on closed rational facts.

Deliverable class **(ii) + (iii)**: a genuine a-priori, NON-circular bound on a concrete
transverse off-diagonal object over a concrete coupling range pushed toward `w*`, plus the
exactly-pinned w→1 obstruction. NOT a `singleStep` alias; NOT `bsq := δ·g`.

---

## 1. The constructed object (a-priori, non-circular)

Temple (`TempleSpectralStabilityDefect`) proved the EXACT equivalence
`realδ_k ≤ 6(1−w_k)² ⟺ ‖P_k^⊥‖² ≤ 6(1−w_k)²(1−w_k³) =: templeThreshold w_k`, reducing the
per-step defect to one per-scale scalar `bsq = ‖P^⊥‖²`. Temple inhabited it only with the
MODEL (`bsq := δ_model·g` — circular). I replace that with a genuinely a-priori scalar built
from the REAL heat-kernel character coefficients:

```
‖P^⊥‖²(w) := plaqActivity w M = Σ_{1≤s<1+M} coeffW w s ,   coeffW w s = (s+1)·w^{C₄(s)},  C₄(s)=s(s+2)
```

This is the excited-rep multi-plaquette character activity — literally "the strength of the
gauge-invariant multi-plaquette interaction one block-spin step generates" coupling the
vacuum/fundamental sector into the excited tower `s≥1`. It is:
- **a-priori** — fixed by the single-plaquette heat-kernel action, no δ, no model;
- **convergent** — a geometric character tail, per-term ratio `coeffW(s+1)/coeffW(s) ≤ 2w⁵`
  (proved `PlaquetteActivity.coeffW_succ_ratio`);
- **non-circular** — reuses only `coeffW` (`RGTransport.charFunc`), never any defect object.

Leading term `coeffW w 1 = 2w³` = the vacuum→fundamental amplitude = the character-expansion
parameter `ρ(w)=2w³`, radius `w* = 2^{−1/3}` (`ρ=1`).

## 2. The strong-coupling bound (increment) — `offDiagActivity_le_threshold`

I re-tuned the convergent character-tail resummation (`CharacterTail.geom_series_le`) with a
tunable closure constant `cQ` to a closed dominator `cQ·w³`, then cleared it under the
threshold by monotonicity. The general theorem takes two DECIDABLE endpoint conditions
(`hrec`: `dimQ 1 + (2·wHi⁵)cQ ≤ cQ`; `hthr`: `cQ·wHi³ ≤ templeThreshold wHi`) and proves,
uniformly in the tower cutoff `M`:

```
plaqActivity w M  ≤  templeThreshold w = 6(1−w)²(1−w³)     for all 0 ≤ w ≤ wHi.
```

Proved instances (mpmath dps=50 pinned, Lean `decide`-certified, `cQ = 5/2`):

| theorem | range `[0, w₀]` | `w₀ / w*` |
|---|---|---|
| `offDiag_le_threshold_half` | `[0, 1/2]`  | 0.630 |
| `offDiag_le_threshold_5_8`  | `[0, 5/8]`  | **0.787** |

**So ‖P^⊥‖ ≤ √6·(1−w)·√(1−w³) is PROVED, a-priori, on `[0, 5/8]` = `[0, 0.787·w*]`**, uniformly
in the excited-tower cutoff. `w₀ = 5/8` is near the true ceiling of THIS object: the exact
infinite excited activity crosses the threshold at `w = 0.63484…` (`= 0.800·w*`, mpmath).

## 3. Temple hook + the sharp residual (class (iii)) — `temple_defect_of_activityDom`

The a-priori bound discharges Temple's `pert`/`bsq ≤ threshold` half OUTRIGHT. Given the sole
OPEN identification `hdom : realδ·(1−w³) ≤ plaqActivity w M` (the real transverse coupling is
at most the excited activity), the per-step defect follows: `realδ ≤ 6(1−w)²`. So the atomic
core is converted into ONE explicit a-priori inequality (`hdom`) against a PROVED a-priori
bound — this is the open `real_defect_identification`, now sharply isolated.

## 4. The exact w→1 obstruction (numerically pinned)

The character parameter `ρ(w)=coeffW w 1 = 2w³` governs the tail's geometric ratio:
- `charParam_lt_one_in_range` — `ρ(5/8) = 250/512 < 1` (proved): the tail converges on-range.
- `charParam_ge_one_beyond_wstar` — `ρ(13/16) = 4394/4096 ≥ 1` (`13/16 > w*`, proved): at `w*`
  the geometric ratio reaches 1, the character resummation DIVERGES, and NO bare a-priori
  character bound survives on `[w*, 1)`.

**Exact remaining obstruction:** the window `[w* , 1)`, `w* = 2^{−1/3} ≈ 0.7937`, where the
convergent strong-coupling character expansion breaks down (`ρ ≥ 1`). There the physical
off-diagonal requires the interacting (renormalized) block-spin effective measure — precisely
the open accumulation `BondMovingStep.BondMovingSummable`. This coincides exactly with
`PushedReconTransferGap`'s `[0, w*)` located-gap window.

## 5. Honest verdict — how far did the a-priori bound push?

- **Proved uniform a-priori bound**: `‖P^⊥‖²(w) ≤ 6(1−w)²(1−w³)` on `[0, 5/8] = [0, 0.787·w*]`,
  all tower cutoffs `M`. This is a genuine construction increment on the sharpest scalar target,
  using a real character object (not δ, not a model, not an alias).
- **Ceilings (mpmath, dps=50)**: this object (activity-as-bsq) ceils at `0.635 = 0.800·w*`; the
  physical amplitude reading `bsq ≤ (Σ coeffW)²` ceils higher at `0.662 = 0.834·w*` (available
  extension, not formalized here); the ultimate radius is `w* = 0.7937` where `ρ=2w³=1`.
- **Adversarial check — does the convergent expansion suffice to `w→1`? NO.** The bound is a
  bare-character strong-coupling resummation whose ratio `ρ=2w³→1` at `w*`; it CANNOT reach
  `w→1`. Two open gaps remain: (a) the on-range `temple` identification `realδ·g ≤ activity`
  (the real-vs-a-priori domination), and (b) the `[w*,1)` window, which genuinely requires the
  interacting measure. Neither is faked or aliased; both are the honest interacting content.
- `F = 1`, `D = 0`, guard = 5. No 4D Yang–Mills mass gap is claimed.
