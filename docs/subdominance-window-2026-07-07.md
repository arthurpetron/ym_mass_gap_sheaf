# The free-quadratic-defect + renormalon-subdominance window test on `[w*, 1)`

**Date:** 2026-07-07 · **Verdict class: (iii) — a sharp residual strip survives; NO closure.**
**Lean:** `lean/YMGap/Continuum/SubdominanceWindow.lean` (builds green, axiom-clean; frontier guard OK).

---

## 0. The objects (all exact / PROVED)

| object | formula | status |
|---|---|---|
| free renormalized defect `δ_free(w)` | `2(1−w)²(2+w)` | PROVED (`RenDefectQuadFactor.renDefect_factor`, `= bondMovingDeltaRen 1 1 w`) |
| model bound target | `realδ ≤ 6(1−w)²` | the per-step defect target |
| **free slack** `slack(w)` | `6(1−w)² − δ_free = 2(1−w)³` | PROVED exact (`dfree_add_slack_eqv_model`) |
| interacting correction | `Δ(w) := realδ(w) − δ_free(w)` | the object to bound |
| renormalon ambiguity | `∼ exp(−π²/g²)`, `g² = −log w` | PROVED asymptotic/fixed-sign (`FieldSpaceRenormalonZ1`) |

The bound `realδ ≤ 6(1−w)²` is **equivalent** to `Δ(w) ≤ slack(w) = 2(1−w)³`
(since `δ_free + slack ≡ 6(1−w)²`, sympy- and Lean-exact).

---

## 1. The renormalon is subdominant EVERYWHERE — but it is the wrong object

mpmath (dps 50), `renormalon(w) = exp(−π²/(−log w))` vs `slack(w) = 2(1−w)³`:

| w | −log w | renormalon | slack | ratio ren/slack |
|---|---|---|---|---|
| 0.001 | 6.91 | 0.117 | ~2.0 | **0.120 (max over (0,1))** |
| 0.5 | 0.693 | 6.5e−7 | 0.25 | 2.6e−6 |
| 0.635 | 0.454 | ~4e−10 | 0.097 | 3.7e−9 |
| w*=0.7937 | 0.231 | 2.8e−19 | 0.0176 | 1.6e−17 |
| 0.9 | 0.105 | 2.1e−41 | 0.002 | 1.0e−38 |
| 0.99 | 0.0101 | 3.3e−427 | 2e−6 | 1.6e−421 |

**Fine scan (step 1e−3):** `max renormalon/slack = 0.1202` at `w≈0.001`; renormalon `< slack`
for **every** `w ∈ (0,1)`. So *if* `Δ` were the renormalon alone, `w₁ = 0`, the window would
trivially overlap `[0,w*)` and close.

**This is the seductive FAKE.** `exp(−π²/g²)` is the *resummation AMBIGUITY* of the fixed-sign,
zero-radius field-space perturbation series (`FieldSpaceRenormalonZ1`: `a_j·a_{j+1}>0`, positive
Borel axis, factorial growth past `j=9`). It is an irreducible *lower* bound on the
non-perturbative content — an uncertainty — **not an upper bound on the full interacting `Δ(w)`.**
Assuming `Δ = renormalon` is exactly the forbidden dodge.

---

## 2. THE DECISIVE ORDER-COUNTING OBSTRUCTION (the catch)

Write `u = 1 − w`. Sympy-exact:

```
δ_free(u) = 6u² − 2u³      model(u) = 6u²      slack(u) = 2u³
```

So **`δ_free` already saturates the model bound `6u²` to SECOND order**; the entire slack
budget for `Δ` is purely **THIRD order**, `2u³`. Therefore `realδ ≤ 6(1−w)²` demands `Δ ≤ 2u³`,
i.e. `Δ` must be genuinely third order or smaller.

But the interacting correction has convergent multi-plaquette / higher-representation pieces
that are **polynomial and generically SECOND order**, `Δ ∼ c·u²`. Such a piece satisfies
`c·u² ≤ 2u³` only for `u ≥ c/2`, i.e. `w ≤ 1 − c/2` — it **VIOLATES on `(1 − c/2, 1)`**, a
neighbourhood of `w = 1`. The renormalon (exp-small) cannot rescue this: the obstruction is a
polynomial second-order piece, not exp-small.

**Machine-checked witness** (`w = 9/10`, `c = 1`; `u=1/10`):

| quantity | value | Lean fact |
|---|---|---|
| slack `= 2u³` | 2/1000 | — |
| unit 2nd-order corr. `c·u²` | 10/1000 | `secondOrder_exceeds_slack`: slack `<` corr |
| `δ_free` | 58/1000 | — |
| model `= 6u²` | 60/1000 | — |
| `δ_free + c·u²` | 68/1000 | `secondOrder_breaks_model`: model `<` δ_free+corr |

Whether the *true* `Δ` is genuinely third order (so the bound holds near `w=1`) is EXACTLY the
open `singleStep` content — **the renormalon-subdominance crack does not establish it.**

---

## 3. The rigorous a-priori bound fails already at `w ≈ 0.635 < w*`

The only rigorous a-priori *upper* bound on the interacting off-diagonal is the character
activity `z₁(w) = Σ_{s≥1}(s+1)w^{s(s+2)} = plaqActivity`, controlled via Temple by
`z₁ ≤ templeThreshold(w) = 6(1−w)²(1−w³)`. mpmath:

- **Full activity crosses the threshold at `w_cross ≈ 0.63484`** (`z₁ = temple`), *below* both
  the Lean-proved range endpoint `5/8 = 0.625` neighbour and `w* = 2^{−1/3} ≈ 0.7937`.
- Even the **leading term alone** `coeffW w 1 = 2w³` exceeds the threshold at `w = 13/20 = 0.65`
  (`0.549 > 0.533`) — Lean fact `charLead_exceeds_threshold`. Since `coeffW w 1 ≤ plaqActivity`,
  the a-priori bound provably fails there.
- `z₁/templeThreshold` **DIVERGES** as `w→1` (`~1/(36(1−w)⁴)`: 257 at 0.9, 2.8e6 at 0.99), so
  the a-priori route is useless at the `w→1` end too.

---

## 4. Where the windows sit (they do NOT overlap)

```
 0 ────────────── 5/8 ── w_cross ─────────── w* ───────────────── 1
 0             0.625    0.6348             0.7937
 |── character a-priori bound ──|                                    (rigorous: [0, 5/8])
 |──────── activity ≤ threshold TRUE ──────|                         (numeric: [0, w_cross])
                                    ▓▓▓▓▓▓▓▓ RESIDUAL STRIP ▓▓▓▓▓▓▓▓▓ [w_cross, 1)
 renormalon subdominance "[w₁,1)":  w₁ = 0  — but bounds the WRONG object (illusory)
```

- **Character / a-priori window:** `[0, 5/8]` rigorously (Lean `offDiag_le_threshold_5_8`);
  numerically extends to `w_cross ≈ 0.6348`.
- **Renormalon-subdominance window:** would be `[0, 1)` (`w₁=0`) *if* `Δ`=renormalon — but that
  bounds the exp-small ambiguity, not `Δ`, so it supplies **no genuine `w₁ < 1`.**
- **Residual:** the strip `[w_cross, 1) ≈ [0.635, 1)` (rigorously `[5/8, 1)`). It is **NOT** a
  bounded strip `[w*, w₁)` with a renormalon-controlled upper end: the upper end `w→1` is NOT
  closed, because `δ_free` saturates the model to 2nd order and any 2nd-order `Δ` breaks it.

---

## 5. HARD-CRITERION verdict

- **(i) inhabit `SingleStepDefectBound` (overlap → all of (0,1)):** NO. Refused — would require a
  rigorous `Δ ≤ slack` on all `(0,1)`, which we do not have (a-priori bound fails past ≈0.635;
  renormalon is not an upper bound on `Δ`). No `:= SingleStepDefectBound` alias written; frontier
  guard confirms all 5 frontier types remain uninhabited.
- **(ii) prove `realδ ≤ 6(1−w)²` on a concrete `[w₁,1)` via free-bound + renormalon-subdominance:**
  NO — cannot. Order-counting shows the slack budget is only 3rd order while the interacting
  correction is generically 2nd order; the renormalon controls only the exp-small ambiguity.
- **(iii) sharp residual:** YES. The explicit residual is the strip `[w_cross,1) ≈ [0.635,1)`
  (rigorously `[5/8,1)`), numerically characterized, with the failure mechanism proved: it is
  **not** a bounded `[w*,w₁)` — the `w→1` end stays open.

**The genuinely-new crack is refuted.** The renormalon subdominance is real (`exp(−π²/g²)` beats
`2(1−w)³` everywhere) but off-object; the true obstruction is the exact order mismatch (3rd-order
slack vs 2nd-order interacting correction) plus the a-priori bound's failure below `w*`. The 4D
Yang–Mills mass gap remains OPEN.

---

## 6. Lean deliverable (`SubdominanceWindow.lean`) — all green, axiom-clean

| declaration | content | axioms |
|---|---|---|
| `dfree_add_slack_eqv_model` | `δ_free + 2(1−w)³ ≃ 6(1−w)²` (exact, factor-out proof) | `propext` |
| `const_collapse` | `(2+w)+(1−w) ≃ 3` (linear terms cancel) | `propext` |
| `secondOrder_exceeds_slack` | unit 2nd-order corr. `>` cubic slack at `w=9/10` | none |
| `secondOrder_breaks_model` | `δ_free + u² > 6u²` at `w=9/10` | none |
| `charLead_exceeds_threshold` | `coeffW(13/20)·1 > templeThreshold(13/20)` | none |
| `renormalon_fixed_sign` | re-export: positive-Borel-axis renormalon | none |
| `subdominance_verdict` | non-vacuous bundle of all the above | `propext` |

`#print axioms` on every load-bearing declaration: `propext` / `Quot.sound` only (most
axiom-free). No `Classical.*`, no `native_decide`, no `ring`/`nlinarith`, no `sorry`. Inhabits no
frontier type; produces no `SingleStepDefectBound`.
