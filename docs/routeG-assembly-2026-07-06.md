# Route G — ASSEMBLING the continuum product floor from the proved regime bounds

**Target.** Assemble the continuum product floor `∏_k(1 − δ_k) > 0` from the two PROVED
per-step defect regime bounds (STRONG channel `δ_k ≤ 6·pMult·(1−w_k)²`; WEAK large-field
`δ_k ≤ K·r^k`), verify the crossover stitch, and pin EXACTLY what remains — does the whole
floor reduce to JUST the identification `GapChannelDomination`?

**Deliverables.** Lean module `lean/YMGap/Continuum/RouteGProductFloorAssembly.lean`
(full `lake build` green, frontier guard OK, axiom-clean), numerics
`verify_routeG.py` (mpmath dps 50 + exact sympy), this report.

---

## 1. The two regimes and the crossover — correctly stated

The real 4D SU(2) block-spin per-step defect `δ_k` is bounded in BOTH regimes:

- **STRONG** (small `k`): channel bound (Routes A/B/C/D). Along AF `1−w_k ≤ C/(k+1)`, so
  `δ_k ≤ 6·pMult·(1−w_k)² ≤ Dδ·1/(k+1)²` — inverse-square, `Dδ = 6·pMult·C²`.
- **WEAK** (large `k`, deep UV): large-field bound (Route E). `δ_k ≤ K·r^k`, geometric,
  `r = exp(−c/A) ∈ (0,1)`.

**Per-step complementarity (verified, mpmath dps 50 — no uncovered `w`):**
block-spin `6(1−w)²<1/2` holds for `w > 0.71132…`; character `w³<1/2` (rate `2w³<1`) holds
for `w < 0.79370…`. The union is ALL of `[0,1]` with a genuine OVERLAP on `(0.7113, 0.7937)`
— NO gap. (Matches `CrossoverDefectUnification.no_uncovered_middle_step`.)

---

## 2. What is PROVED in Lean-core (axiom-clean `propext`/`Quot.sound` only)

`RouteGProductFloorAssembly.lean`, every load-bearing decl `#print axioms` = `[propext]` or
`[propext, Quot.sound]` — no `Classical.*`, no `sorryAx`, no `native_decide`. LEAN-CORE
(`Q'`/`CReal`), no Mathlib/ring.

| declaration | statement | axioms |
|---|---|---|
| `tailSum_le_add_of_termwise` | union bound `δ_k ≤ a_k+b_k` ⟹ `Σδ ≤ Σa + Σb` (split core) | propext |
| **`crossover_tailSum_le`** | **THE CROSSOVER STITCH.** per-step disjunction (`δ_k ≤ Dδ/(k+1)²` ∨ `δ_k ≤ K·r^k`) ⟹ `Σ_{k<N} δ_k ≤ 2·Dδ + K/(1−r)`, uniform in `N` | propext, Quot.sound |
| **`twoRegimeProductFloor`** | **`∏(1−δ_k) > 0` from the regime bounds.** `δ_k∈[0,½]` + crossover ⟹ positive CReal floor `c` (rational witness `ε>0`) with `c ≤ ∏_{k<n}(1−δ_k)` uniformly in `n` | propext, Quot.sound |
| **`twoRegimeDefectGapRecursion`** | **the whole `DefectGapRecursion`** from regime bounds + the ONE open identification `hrec` | propext, Quot.sound |
| **`twoRegime_continuum_floor`** | positive uniform floor `∀k, ε·physGap 0 ≤ physGap k`, `0 < ε·physGap 0` | propext, Quot.sound |
| **`wholeFloor_of_gapChannelDomination`** | **THE PUNCH-LINE.** the entire true-margin floor from `GapChannelDomination` alone | propext, Quot.sound |

**The crossover stitch (heart).** The disjunction + nonnegativity of the un-used majorant
gives the UNION bound `δ_k ≤ Dδ·1/(k+1)² + K·r^k` at EVERY `k` (elementary: `x≤A ⟹ x≤A+B`
for `B≥0`, and symmetrically). Then `tailSum_le_add_of_termwise` splits the sum, closed by
the two PROVED budgets:
- STRONG: `invSq_budget_bound` (`Σ 1/(k+1)² ≤ 2`, telescoping — `π²/6 = 1.6449… ≤ 2`);
- WEAK: `geomBudget_le` (`Σ r^k ≤ 1/(1−r)`, `(1−r)·geomSum = 1−r^N ≤ 1`).

So `Σδ ≤ 2Dδ + K/(1−r) < ∞`. This is exactly `Σδ<∞` — the ONLY summability the product
floor needs (it does NOT need `Σδ<1`).

**Why the EXPONENTIAL floor, not Weierstrass.** The honest AF middle budget
`Σ 6(1−w)²` over `w = ½,⅔,¾` is `61/24 ≈ 2.5417 > 1` (`CrossoverDefectUnification.middle_
additive_budget_exceeds_one`), so the Weierstrass floor `∏(1−δ) ≥ 1−Σδ` goes NEGATIVE and
is USELESS. `twoRegimeProductFloor` therefore feeds the crossover budget `R = 2Dδ + K/(1−r)`
into the PROVED `ExpProductFloor.sum_loss_to_productFloor_exp`, whose floor `e^{−2R} > 0`
for ALL finite `R` (verified `e^{−2R}>0` at `R=1.2` and `R=14`). This is the decisive
product-vs-additive point the task flagged.

**The `δ_k ≤ ½` (tail) condition — honestly carried.** The exp floor needs `δ_k ≤ ½`. The
STRONG bound `6(1−w)²` EXCEEDS ½ at small `w` (`= 4.17` at `w=1/6`, `= 1.5` at `w=½`), so
`δ≤½` holds only on the deep-UV TAIL `k ≥ k₀` — exactly where `DominantModeRecursion` puts
it (`renDefect_le_half`). `twoRegimeProductFloor` carries `hδhalf : ∀k, δ k ≤ ½` as an
EXPLICIT hypothesis; the finite strong-coupling head is the separately-PROVED fixed-spacing
gap. Nothing hidden.

---

## 3. Does the floor assemble MODULO only the identification? — YES

`twoRegimeDefectGapRecursion` is a CONDITIONAL producer: given the two regime bounds
(`hregime`, `hδhalf`) AND the single OPEN field `hrec : (1 − δ_k)·physGap_k ≤ physGap_{k+1}`,
it builds a FULL `DefectGapRecursion` — `defect = δ`, product floor `= ε·physGap 0 > 0`
(the exp floor via the `geRat`+`leRat`→`Q'` bridge `le_of_geRat_leRat`), and
`continuum_floor_of_defectRecursion` then yields the positive uniform floor. The SOLE open
input is `hrec` — the identification.

`hrec` is LITERALLY `GapChannelDomination.domination` = `SingleStepDefectBound.singleStep`
= the `DefectGapRecursion.recursion` field for the true margin. `wholeFloor_of_
gapChannelDomination` makes this exact: for the MODEL/channel defect `afDefectSeq afr`
(whose `δ<1`, `Σδ<∞`, and product floor `afFloorEps` are ALREADY PROVED upstream), a
`GapChannelDomination` `G` yields the ENTIRE positive continuum floor for `G.trueMargin`
via the proved chain `gapChannelDomination_to_singleStep → defectRecursion_of_singleStep →
continuum_floor_of_defectRecursion`.

**Verdict: the continuum product floor assembles MODULO ONLY the identification
`GapChannelDomination`.** On the assembly side there is NO residual gap:
- `δ_k < 1` per step — covered by complementarity (no uncovered `w`);
- `Σδ < ∞` — PROVED (`crossover_tailSum_le`, both regime budgets finite and stitched);
- `∏(1−δ) > 0` — PROVED (`twoRegimeProductFloor`, exponential floor, valid though `Σδ>1`).

The crossover stitch genuinely covers all `k` (adversarial check: the disjunction is
per-step total by complementarity; there is no `k` where NEITHER regime bound applies), and
`Σδ` is genuinely finite along AF (`2Dδ + K/(1−r)`; the earlier `Σδ ≈ 2.54 > 1` finding is
FINITE — fine for the product floor, which needs only `Σδ<∞`).

---

## 4. Adversarial honesty ledger

- **NO frontier bundle inhabited.** Frontier guard UNCHANGED at 5 (`GapChannelDomination`,
  `SingleStepDefectBound`, `TrueMarginRecursion*`, … all still unconditionally uninhabited).
  Every result is a PRODUCER with open binders (the regime bounds, and for the floor the
  identification `hrec`). NO 4D Yang–Mills mass gap is claimed.
- **NO fake `δ`.** No free field, no `δ := 0`. The producers take a GENERAL `δ` constrained
  by the genuine regime bounds; the non-vacuous content is the PROVED crossover-stitch
  summability and exp product floor about concrete `recipSqSucc` / `geomMajorant` / `expNeg`
  objects.
- **The regime bounds' own status.** STRONG (`δ_model ≤ 6p(1−w)²`) is PROVED
  (`bondMovingDeltaRen_le_sixp`), inverse-square along AF via the named AF rate. WEAK
  (`δLF ≤ K·r^k`) is the NAMED `LargeFieldSuppression` input (geometric summability proved;
  the physical bound uninhabited for real 4D, per Route E). Both are the two physical halves
  OF `GapChannelDomination` itself (Route D small-field + Route E large-field), so folding
  them into the single identification is faithful, not a hidden second gap.
- **The `δ≤½` tail restriction is stated, not smuggled** (§2). The finite head is the proved
  strong-coupling gap.

---

## 5. Build / guard / axioms

```
$ lake build
info: YMGapGuard.lean: frontier-guard OK: 5 Clay-frontier types unconditionally
      uninhabited across YMGap.*
Build completed successfully (686 jobs).
```

`#print axioms` for all 10 load-bearing decls: `[propext]` or `[propext, Quot.sound]` only.
No `Classical.*`, no `sorryAx`, no `native_decide`, no `sorry`.

Numerics (`verify_routeG.py`, mpmath dps 50 + exact sympy): complementarity covers `[0,1]`
with overlap; `Σ1/(k+1)² = π²/6 ≤ 2`; `Σr^k = 1/(1−r)` exactly; middle budget `61/24 > 1`
(⟹ Weierstrass fails, exp floor needed); `e^{−2R} > 0` all finite `R`; `δ≤½` needs the tail.

---

## 6. HONEST VERDICT

**Does the continuum floor now reduce to JUST `GapChannelDomination` (the identification), or
is there another genuine gap?**

It reduces to **JUST the identification.** The two-regime bounds ASSEMBLE — via the PROVED
crossover stitch (`Σδ ≤ 2Dδ + K/(1−r) < ∞`, both budgets stitched), the complementarity
(`δ<1`, all `k` covered, no gap), and the PROVED exponential product floor (`∏(1−δ)>0`,
valid though `Σδ>1`) — into a full `DefectGapRecursion` and positive uniform continuum floor,
CONDITIONAL on the single per-step recursion `(1−δ_k)·physGap_k ≤ physGap_{k+1}`. That
recursion IS `GapChannelDomination.domination`. There is NO other genuine gap on the assembly
side: summability, per-step `δ<1`, and the product floor are all machine-checked here (and
`afFloorEps` for the model defect upstream).

The SOLE remaining open content is the identification itself — the genuine Bałaban/MRS
small-field+large-field theorem that the real per-step degradation of the true dimensionless
margin is bounded by the model defect `(1 − afDefectSeq afr)`. Its two physical halves are
the higher-rep character tail (Route D, strong-coupling proved) and the large-field geometric
suppression (Route E, summability proved); together they discharge `GapChannelDomination`.
The 4D Yang–Mills mass gap remains OPEN; nothing is faked.
