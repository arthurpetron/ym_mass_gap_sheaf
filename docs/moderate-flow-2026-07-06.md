# The moderate RG-flow middle window: unified with `DefectGapRecursion`, and pinned

**Deliverable.** New Lean file
`lean/YMGap/Continuum/CrossoverDefectUnification.lean` (built, imported in
`YMGap.lean`, full `lake build` green = **665 jobs**, `YMGapGuard` **OK** = 5
Clay-frontier types unconditionally uninhabited). Every load-bearing declaration is
axiom-clean: `[propext]`, `[propext, Quot.sound]`, or **no axioms** (all six numeric
`decide` lemmas are axiom-free). No `sorry`, no `Classical.*`, no `native_decide`.

I did **not** close the continuum gap. I (1) formalized that the whole floor rests on
the ONE existing named RG wall `DefectGapRecursion`, (2) exhibited the exact
structural reason the middle window resists (additive budget vs product floor), and
(3) proved the moderate middle is a **finite** window with **no uncovered summed
sub-window**. Honest verdict at the bottom.

---

## TASK 1 — UNIFY: the whole floor rests on ONE existing named RG wall

`fullFloor_of_defectRecursion (D : DefectGapRecursion)` gives the **entire** positive
continuum floor

    (0 < D.prodFloor) ∧ ∀ k, D.prodFloor ≤ D.physGap k

from a single `DefectGapRecursion` object, via its **product floor**
`∏(1 − δ_k) ≥ prodFloor > 0` (= `continuum_floor_of_defectRecursion`). Its **only**
open field is `recursion` (the per-step true-margin gap-degradation law). Everything
else is already proved:

| ingredient | status | source |
|---|---|---|
| strong-coupling anchor `107/108` | PROVED | `RealCorrMass` / `CrossoverAnchorFloor.strongAnchor_ge_half` |
| deep-UV AF tail `δ_k ≤ D/(k+1)²`, `Σ ≤ 2D` | PROVED | `AFDeepUVSummability`, `uv_tail_bound` |
| adequacy split (crossover + tail) | PROVED | `NetDriftBudgetSplit.budget_split_bound` |
| summability `∏(1−δ)>0` | PROVED | `SummabilityCapstone.renormalized_gap_of_AFRate` |
| per-step middle complementarity | PROVED | `CharacterWindowCeiling` + block-spin (below) |
| **per-step `recursion` for TRUE margin** | **OPEN** | `TrueMarginRecursion` (uninhabited) |

`fullFloor_of_dominantMode` shows the floor is **unconditional** for the dominant-mode
survival-product *surrogate* margin (via the proved
`DominantModeRecursion.dominantModeRecursion`), and `crossoverDefect_ofDefectRecursion`
gives the literal identification: the middle obligation `CrossoverWindowDefect`'s
δ-sequence **is** a `DefectGapRecursion`'s defect sequence.

### The exact single remaining obligation

`single_remaining_obligation (T : UniformCouplingFromAF.TrueMarginRecursion)` proves
that IF the honest named residual `TrueMarginRecursion` is inhabited — its `recursion`
field being the per-step non-abelian multi-link 4D gap-degradation law for the **true**
dimensionless margin `m_lat(a_k)/a_k` — THEN the positive continuum floor holds for
that true margin. That is the exact single obligation on which the entire Clay
continuum gap rests. It is **not** inhabited (guard OK).

---

## The KEY structural insight — why the middle resists: ADDITIVE budget vs PRODUCT floor

`CrossoverAnchorFloor`'s additive route needs the crossover **sum** `Σ_{k<K} δ_k < 1`
(so the coefficient `1 − Σδ` stays positive). The honest RG defect over the moderate
middle **violates** this:

```
middle_additive_budget_exceeds_one :
   1 < 6·((1/2)² + (1/3)² + (1/4)²)          -- = 6·(0.4236) = 2.542 > 1   (axiom-free decide)
```

The block-spin defect `6(1−w)²` summed over the three canonical middle margins
`1−w = 1/2, 1/3, 1/4` is `≈ 2.54 > 1`, so `1 − Σδ` goes **negative** — the additive
`CrossoverWindowDefect` route is **dead** on the real RG defect. The `DefectGapRecursion`
**product** floor `∏(1 − δ_k) > 0` needs only `Σδ < ∞` (the product converges to a
positive value), **not** `Σδ < 1`. So the product route succeeds exactly where the
additive middle budget fails — this is *why* the whole floor must rest on the
`DefectGapRecursion` wall, not on the additive budget.

For the AF regime this is made concrete: `crossoverDefect_ofInvSqDefect` proves the
**K-uniform** crossover budget `tailSum δ 0 K ≤ 2A` from an inverse-square majorant
`δ_k ≤ A/(k+1)²` — the `Σδ<∞` content of the product floor turned into a finite bound.

---

## TASK 2 — ATTACK the moderate flow

### (a) FINITE window: `K_mid = 3` on the canonical trajectory

Canonical AF trajectory `w_k = 1 − 1/(k+1)`: `w_0=0, w_1=1/2, w_2=2/3, w_3=3/4,
w_4=4/5`. The middle `(1/6, 7/9)`:

```
middle_is_three_steps :
   (1/6 < 1/2 < 7/9) ∧ (1/6 < 2/3 < 7/9) ∧ (1/6 < 3/4 < 7/9)
   ∧ (0 < 1/6)  [w_0 below]  ∧ (7/9 < 4/5)  [w_4 above]        (axiom-free decide)
```

The middle contains **exactly three steps** `k ∈ {1,2,3}`; `w_0` is below `1/6`
(strong-coupling anchor), `w_4` is above `7/9` (character ceiling). So `K_mid = 3` — a
**finite, decidable** budget. More generally (TASK 2b): because the moderate
`β(g²)=O(1)`, the flow moves by O(1) per step across `(1/6,7/9)`, so only finitely
many `k` land in the middle — the middle budget is always a finite check, unlike the
harmonic deep-UV tail where the ratio `→1`.

### (b) Numeric estimate of the moderate contraction `ρ`, and whether it clears

The harmonic AF flow has margin ratio `(1−w_{k+1})/(1−w_k) = (k+1)/(k+2) → 1` — it does
**NOT** contract geometrically (`ρ_k → 1`). The passing numeric instance in
`CrossoverFlowContraction.numeric_budget_clears` (`Bcrossδ+2Dδ = 0.3728 < 1/2`) assumes
`ρ² = 1/4` (i.e. `1−w` halves each step), which the harmonic flow does **not** satisfy.
Concretely, starting the crude block-spin budget from the character handoff `w≈0.8`
(`k=4`) and summing the harmonic tail gives

    6·Σ_{k≥4} 1/(k+1)²  =  π² − 6·(1 + 1/4 + 1/9 + 1/16)  ≈  1.33  >  1,

so the crude-additive harmonic block-spin budget does **not** clear even `< 1`. This is
the honest content behind the doc's caveat. **However** — the product `∏_{k≥4}(1 −
6/(k+1)²)` still converges to a *positive* value (`Σ < ∞`, not `Σ < 1`), which is why
the product-floor route (proved `renormalized_gap_of_AFRate`, using the renormalized
`δ_ren < 1/2` past the cutoff, not the crude `6(1−w)²`) closes the deep-UV
unconditionally while the additive route cannot. **Starting the block-spin budget at
`w=7/9` instead of `1/6` does NOT by itself clear the additive budget** on the harmonic
flow; the closure is the product floor, not a smaller additive window.

### (c) OVERLAP CLOSURE: the truly-uncovered summed sub-window is EMPTY

The two mechanisms have opposite scaling and cover the middle per-step with overlap:

```
middle_char_valid :   w_1³, w_2³, w_3³  all  < 1/2      -- character ρ=2w³<1 on ALL 3 middle steps
w4_blockspin_covers : w_4³ > 1/2  (char fails)  AND  6(1−w_4)² = 6/25 < 1/2  (block-spin covers)
w3_in_overlap :       w_3³ < 1/2  AND  6(1−w_3)² < 1/2  -- BOTH valid at w_3 = 3/4 (non-empty overlap)
no_uncovered_middle_step :  every middle step char-covered, w_4 block-spin-covered
```

(all axiom-free `decide`.) Per-step coverage of `[0,1]`: **character** below the
ceiling `7/9`, **block-spin** above `≈0.711`, overlapping on `(0.711, 0.778)` (the
canonical `w_3 = 0.75` sits inside it). Since every middle step is character-valid *by
construction* (the middle's upper edge **is** the character ceiling `7/9`) and the
first step past the ceiling is block-spin-covered, **there is no step where both
mechanisms fail — the truly-uncovered summed sub-window is EMPTY.**

---

## HONEST VERDICT

**(a) Is the whole gap now one existing named RG wall?** **YES.**
`fullFloor_of_defectRecursion` puts the entire positive continuum floor on a single
`DefectGapRecursion` — the *existing* named wall — with the anchor (`107/108`), deep-UV
AF tail, adequacy, summability, and per-step middle complementarity **all proved**. The
sole open field is `recursion` for the true margin, named as the uninhabited
`TrueMarginRecursion` (`single_remaining_obligation`). The unconditional floor already
holds for the dominant-mode *surrogate* margin (`fullFloor_of_dominantMode`).

**(b) Is the moderate contraction closeable/reducible, or the genuine Bałaban
residual, and how narrow is the truly-uncovered summed sub-window?**

- The **truly-uncovered summed sub-window is EMPTY** on the canonical trajectory
  (`no_uncovered_middle_step`): character covers the whole middle `(1/6,7/9)`, block-spin
  covers `w ≥ 4/5`, overlapping at `w=3/4`. There is no coverage gap to close.
- The moderate middle is a **FINITE** window (`K_mid = 3`, `middle_is_three_steps`), so
  the residual is a finite/decidable budget, not an infinite summation.
- What genuinely resists is **not an uncovered window** but the **summed middle
  contraction**: the harmonic AF flow has `Σδ ≈ 2.54 > 1` over the middle
  (`middle_additive_budget_exceeds_one`), so the **additive** route is dead. Closure must
  go through the **product** floor `∏(1 − δ_k) > 0` (which needs only `Σδ < ∞`), i.e. the
  finite `K_mid`-step per-step contractions must compose to a positive product. That
  composition is precisely the `DefectGapRecursion.recursion` field on the finite middle
  — the **genuine Bałaban residual**, now finite and decidable *given the trajectory and
  the true-margin per-step law*, but still uninhabited for the real 4D non-abelian
  multi-link step.

**Net:** the continuum gap is reduced to ONE existing named wall with a **finite,
per-step-fully-covered, no-coverage-gap** moderate window; the irreducible core is the
product-floor composition on that finite window (the true-margin `recursion` field),
which the surrogate discharges but the genuine 4D margin does not. **Clay target: OPEN.
No 4D Yang–Mills mass gap is claimed; nothing is faked.**

## Files
- `lean/YMGap/Continuum/CrossoverDefectUnification.lean` (new; imported in `YMGap.lean`).
- Builds on: `CrossoverFlowContraction`, `CrossoverAnchorFloor` (`CrossoverWindowDefect`,
  `crossoverDefect_ofPerStep`, `tailSum_le_ofNat_mul`), `ContinuumClosureProgram`
  (`DefectGapRecursion`, `continuum_floor_of_defectRecursion`), `NetDriftBudgetSplit`
  (`uv_tail_bound`), `DominantModeRecursion.dominantModeRecursion`,
  `UniformCouplingFromAF.TrueMarginRecursion`.
