# The crossover defect as a flow-contraction obligation + character-fail complementarity

**Deliverable.** New Lean file `lean/YMGap/Continuum/CrossoverFlowContraction.lean`
(built, imported in `YMGap.lean`, full `lake build` green = 663 jobs, `YMGapGuard`
OK = 5 Clay-frontier types uninhabited). Every load-bearing declaration is
axiom-clean: `[propext]`, `[propext, Quot.sound]`, or *no axioms* (the three numeric
`decide` lemmas). No `sorry`, no `Classical.*`, no `native_decide`.

I did **not** close the crossover. I sharpened the single remaining obligation
`CrossoverWindowDefect δ ε K` two ways and established the character-fail
complementarity at the per-step level. Honest verdict at the bottom.

---

## Task 1 — FLOW BOUND: the crossover budget is now an explicit, K-independent
## flow-contraction obligation `ρ² < 1`

Along the RG flow toward the UV the weak-coupling margin `m_k := 1 − w_k` decreases
(`w_k → 1`). If it contracts geometrically, `m_{k+1} ≤ ρ·m_k` (`0 ≤ ρ`, `ρ² < 1`),
the squared margins contract with rate `t = ρ²`, and the **geometric partial-sum
bound** gives a K-uniform budget. Proved chain:

```
geomTelescope          (1−t)·Σ_{k<K} t^k  ≃  1 − t^K                 -- telescoping identity
geomPartialSum_le      Σ_{k<K} t^k  ≤  1/(1−t)                        -- K-uniform, via le_divPos_of_mul_le
contraction_pow        a_{k+1} ≤ t·a_k , a≥0 ⟹ a_k ≤ a_0·t^k
geom_budget_bound      Σ_{k<K} a_k  ≤  a_0 · 1/(1−t)                  -- the K-independent contraction sum
sq_contraction         m_{k+1} ≤ ρ·m_k ⟹ m_{k+1}² ≤ ρ²·m_k²          -- squared margins contract with ρ²
crossover_sq_sum_le    Σ_{k<K} m_k²  ≤  m_0² · 1/(1−ρ²)
crossover_sum_le       Σ_{k<K} δ_k   ≤  6p · m_0² · 1/(1−ρ²)  =: Bcrossδ
```

The last line uses the per-step quadratic defect `δ_k ≤ 6p·m_k²`
(`RenDefectQuadFactor.bondMovingDeltaRen_le_sixp`). So

> **`Bcrossδ = 6p · (1 − w_0)² / (1 − ρ²)`** — explicit, closed, K-independent.

`crossoverDefect_ofFlowContraction` inhabits the single named obligation
`CrossoverWindowDefect δ ε K` from this ONE flow-contraction fact (`ρ² < 1`) plus a
per-step additive cap `ε_j ≤ εmax` (giving `Bε = K·εmax`). It **consumes** the
contraction hypothesis — nothing is inhabited unconditionally, so the frontier
obligation stays open and the guard passes.

**Numeric estimate + the total-budget target `Bcrossδ + 2Dδ < 1/2`.** Instantiated
at `p = 1`, handoff margin `m_0 = m* = 21/100`, `ρ² = 1/4` (so `1/(1−ρ²) = 4/3`),
`Dδ = 1/100`:

```
Bcrossδ          = 6·(21/100)²·(4/3) = 3528/10000 = 0.3528        (assembled_Bcross_value, decide)
Bcrossδ + 2·Dδ   = 0.3528 + 0.02     = 0.3728  < 1/2              (numeric_budget_clears, decide)
```

With the proved anchor `margin 0 = 107/108` and no additive erosion this clears the
anchor-dominance and leaves a floor `(1 − 0.3728)·(107/108) ≈ 0.62 > 0`. **So the
target holds** for this instance — but it is genuinely tight and depends on both the
handoff `m_0` and the contraction `ρ`: e.g. starting the block-spin sum from the
strong anchor `w_0 = 1/6` (`m_0 = 5/6`) gives `Bcrossδ ≈ 6·0.69/(1−ρ²) ≈ 8 ≫ 1/2` —
hopeless, because at strong coupling `1 − w` is O(1). The budget only clears when the
block-spin sum starts **near** `w = 1` (small `m_0`) and `ρ` is a genuine contraction.

## Task 2 — NEW LEVERAGE: the block-spin defect controls the character-fail window

The two mechanisms have **opposite** scaling and are complementary:

| mechanism | rate / defect | valid where |
|---|---|---|
| character (Wilson) | `ρ_char = 2w³ < 1` | `w < 2^{−1/3} ≈ 0.7937` (proved to `7/9`, `CharacterWindowCeiling`) |
| block-spin | `δ = 6p(1−w)²` small | `w` near `1` (`p=1`: `δ<1/2` ⟺ `w > 0.711`) |

The block-spin defect is smallest exactly where characters fail (`w ≥ 2^{−1/3}`). At
the concrete handoff `w* = 79/100`:

```
handoff_in_overlap        w*³ = 493039/1000000 < 1/2   AND   6·m*² = 2646/10000 < 1/2
```

`w*` is **below** the character ceiling (so `ρ_char(w*) < 1`, character still valid)
**and** above the block-spin threshold (block-spin per-step `< 1/2`) — the two windows
`[0, w*]` and `[w*, 1]` cover `[0, 1]` with a clean handoff, **no coverage gap**.

The decisive lemma:

```
blockspin_perstep_le_handoff :  w* ≤ w ≤ 1  ⟹  6·(1−w)²  ≤  6·m*²  <  1/2     -- UNCONDITIONAL
```

So on the **entire** character-fail region `(2^{−1/3}, 1] ⊂ [w*, 1]` the block-spin
per-step defect is provably `< 1/2` — no hypothesis. This is a genuine advance: the
block-spin/net-drift controls exactly the sub-window the character mechanism cannot
reach (`WindowOverlap` / `RGClusteringTransport` left open).

**Is `CrossoverWindowDefect` inhabitable on the character-fail region? Per-step: YES,
unconditionally. Summed: needs the flow input.** The per-step defect is bounded
unconditionally, but the *summed* budget over `[w*, 1]` (an infinite tail `w → 1`)
would diverge without contraction. It splits cleanly: the deep-UV part `k ≥ K` is the
AF `1/k²` tail (`AFDeepUVSummability`, proved), and the finite crossover part `k < K`
is the `CrossoverWindowDefect`, whose budget is the flow-contraction `Bcrossδ` of Task 1.
So the character-fail window's summability is **reduced** — per-step unconditionally,
summed to the flow-contraction fact — but not unconditionally closed. I inhabit
nothing unconditionally on the full frontier (guard OK); the honest closure is
per-step + a concrete passing budget instance.

## Task 3 — UNIFY / REDUCE

**(i) Explicit flow-contraction obligation.** `fullFloor_of_flowContraction` gives the
**entire** positive continuum floor from a single geometric flow-contraction fact
`ρ² < 1` (plus the proved anchor, the AF deep-UV tail, and the decidable
anchor-dominance). The whole obligation is reduced to: *does the finite crossover
flow contract with `6p·m_0²/(1−ρ²) < 1 − 2Dδ`?* — a quantitative flow fact.

**(ii) Unification with `DefectGapRecursion`.** The crossover budget sum
`Σδ_k ≤ Bcrossδ` and the `DominantModeRecursion.dominantModeRecursion` survival-product
floor `∏(1 − δ_k) ≥ floorEps > 0` are two views of the **same** geometric-summability
fact (a summable `δ_k ≤ 6p(1−w_k)²` ⇒ positive floor). Documented in the module;
`fullFloor_of_flowContraction` is the crossover-side analogue of
`continuum_floor_of_defectRecursion`.

---

## HONEST VERDICT

The single remaining obligation of the continuum gap is now, precisely:

- **(a) an explicit flow-contraction obligation `ρ² < 1`** — `crossover_sum_le` /
  `crossoverDefect_ofFlowContraction` reduce the whole crossover budget to the closed
  form `Bcrossδ = 6p·(1−w_0)²/(1−ρ²)`, and `fullFloor_of_flowContraction` puts the
  entire floor on that ONE fact. A concrete instance clears `Bcrossδ + 2Dδ < 1/2`
  (`numeric_budget_clears`). **Caveat (adversarial):** the *true* AF flow is harmonic
  (`m_k ∼ 1/k`, ratio `ρ_k → 1`), so no *uniform* `ρ < 1` holds in the deep UV — the
  flow contraction holds only over a *finite* crossover window with a window-dependent
  `ρ`. So `ρ² < 1` is a genuine named input, not a free fact; the deep-UV tail is
  handled separately by the AF `1/k²` route.

- **(b) unified with `DefectGapRecursion`** — the crossover budget sum and the
  dominant-mode survival-product floor are the same summable-defect content;
  `fullFloor_of_flowContraction` is the explicit bridge.

- **(c) partially closed on the character-fail sub-window `(2^{−1/3}, 1]`** — the
  block-spin per-step defect is `< 1/2` there **unconditionally**
  (`blockspin_perstep_le_handoff`), the opposite scaling to characters, and the two
  windows cover `[0,1]` with a clean handoff at `w* = 79/100` (`handoff_in_overlap`).
  The *summed* budget over that window still needs the flow-contraction of (a) — so it
  is reduced (per-step closed, summed reduced), not unconditionally closed.

**What still resists:** the quantitative flow fact — that the finite crossover from the
character ceiling to the AF deep-UV cutoff has a strong enough effective `ρ` (few enough
steps) that `6p·m_0²/(1−ρ²) + 2Dδ < 1`. The numeric instance shows this *can* hold; it
is not proved for the genuine 4D AF trajectory. **Clay target: OPEN. No 4D Yang–Mills
mass gap is claimed; nothing is faked.**

## Files

- `lean/YMGap/Continuum/CrossoverFlowContraction.lean` (new; imported in `YMGap.lean`).
- Builds on: `CrossoverAnchorFloor` (`CrossoverWindowDefect`, `strongAnchor`,
  `fullFloor_reduced_to_crossover`), `RenDefectQuadFactor` (`bondMovingDeltaRen_le_sixp`,
  the `6p(1−w)²` defect), `SummableInverseSquare.tailSum`, `Geometric.Q'.pow`, the
  `divPos`/`recipPos` order lemmas. Complements `CharacterWindowCeiling` (the ceiling
  `2^{−1/3}`) and `DominantModeRecursion` (the survival-product floor).
