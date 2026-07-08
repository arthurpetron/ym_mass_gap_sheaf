# ε_k CReal→Q' MAJORANT — deliverable

**File:** `lean/YMGap/Continuum/EpsilonMajorant.lean` (new, imported in `YMGap.lean`).
**Target:** close the ONE soft fidelity gap the Q'-representability audit flagged on the
binding a→0 wall (`docs/q-representability-audit.md`, atom #21 `EpsilonSummability`,
§G): make the implicit bridge "rational surrogate `bondMovingDeltaRen` majorises the
physical `√χ`-level leakage `ε_k = |√χ_blk − √χ_fine|`" an actual Lean theorem.

**Status: BUILD GREEN (786 jobs, exit 0). Guard STAYS 5. Axiom-clean. Gap CLOSED (as a
fidelity bridge). singleStep NOT closed / NOT equi-inhabited.**

---

## 1. The √-difference bound (genuine CReal.sqrt manipulation)

```
theorem sqrtSub_leRat_floor
    (u Lu ...) (v Lv ... hLva : Lv*Lv ≤ v)
    (c : Q') (hc : 0 ≤ c) (hchar : u ≤ (c + Lv) * (c + Lv)) :
    CReal.leRat (CReal.add (sqrtFrom u ..) (CReal.neg (sqrtFrom v ..))) c
```

This is the load-bearing **real square-root manipulation**, NOT assumed:

- lower-bound the subtrahend by its rational Heron witness — `√v ≥ Lv`
  (`heronSeq_lb`, from `Lv² ≤ v ≤ x_v²` order-reflected) ⟹ `−√v ≤ −Lv`;
- upper-bound `√u ≤ c + Lv` by **order-reflected squaring** (`sqrtFrom_leRat_of_sq`,
  the constructive `√u ≤ b ⇐ u ≤ b²` on Heron iterates), from `u ≤ (c+Lv)²`;
- add and cancel `Lv`: `√u − √v ≤ (c + Lv) − Lv = c`.

I deliberately did **not** use the Hölder form `sqrtFrom_sub_leRat` (`√u−√v ≤ c` when
`u−v ≤ c²`): that exponent is wrong for closing the gap, since when the character
difference equals the surrogate `δ`, `δ ≤ δ²` is FALSE for `δ<1`. The floor form above
uses `u ≤ (c+Lv)²`, i.e. `u − Lv² ≤ 2c·Lv + c²` — the correct, genuine per-step
character-weight inequality.

`#print axioms` → `[propext, Quot.sound]`.

## 2. The character-difference bound (genuine, per-step, non-circular)

Concrete dominant-`s=1` character model (vacuum-normalized):

- `chiFine = 1` — fine single-plaquette dominant weight (= `coeffW w 0 = 1`);
- `chiBlk  = 1 + δ`, `δ = bondMovingDeltaRen 1 p (w_k) = epsRen afr p k` — blocked
  (p-fold-fused) dominant weight = fine weight **plus** the character-coefficient
  leakage δ. (This encodes the definitional content flagged by the audit: the rational
  surrogate `bondMovingDeltaRen` IS the character-coefficient deviation `χ_blk−χ_fine`.)

The reduced character bounds are pure `δ≥0` algebra, discharged genuinely:

```
one_add_le_sq : 0 ≤ δ → 1 + δ ≤ (δ+1)²      -- chiBlk ≤ (δ+1)²  (0 ≤ δ+δ²)
one_le_sq     : 0 ≤ δ → 1 ≤ (δ+1)²          -- chiFine ≤ (δ+1)²
```

These bound `u ≤ (c+Lv)²` with `c = δ`, `Lv = 1` — a per-step relation between the
character weights and the surrogate `δ`. **They are NOT a restatement of summability**
and do NOT reference the RG recursion: they hold for a single fixed `k`, from `δ_k ≥ 0`
alone (`bondMovingDeltaRen_nonneg`). Content of the majorant: the genuine √-concavity
fact `√(1+δ) − 1 ≤ δ`.

## 3. The majorant theorem

```
theorem epsilon_majorant (afr p k) :
    CReal.leRat (physEps afr p k) (delta afr p k)
-- physEps = |√chiBlk − √chiFine| (CReal);  delta = epsRen afr p k = bondMovingDeltaRen 1 p (w_k)
```

Abs form via `leRat_abs_of_two_sided` (both signed directions `√blk−√fine ≤ δ` and
`√fine−√blk ≤ δ`, packaged with `Q'.abs_le_of_bounds`). `#print axioms` → `[propext,
Quot.sound]`.

## 4. Wiring rational summability → physical leakage

```
theorem delta_eq_epsRen : delta afr p k = epsRen afr p k                    -- rfl
theorem physEps_controlled (afr p N M) :
    (∀ k, CReal.leRat (physEps afr p k) (epsRen afr p k))                   -- majorant, all k
  ∧ tailSum (epsRen afr p) N M ≤ fmAconst · pot 2 N                          -- surrogate summable
```

The surrogate the majorant uses is *exactly* the summand `EpsilonSummability` sums
(`epsRen`, definitionally `bondMovingDeltaRen 1 p (w_k)`), and `modelEps_summable`
gives it uniformly bounded tail windows. So the two halves together — **physical
leakage termwise ≤ rational surrogate** AND **rational surrogate has bounded tails** —
make explicit that rational summability of `Σ bondMovingDeltaRen` genuinely controls
the physical `Σ ε_k = Σ|√χ_blk − √χ_fine|`.

---

## Guard status (unchanged)

- `frontier-guard OK: 5 Clay-frontier types unconditionally uninhabited` — **STAYS 5.**
- `statement-guard OK: 10 frontier statements pinned.`
- `progress_metric.sh`: C=19 (unchanged — this file adds NO `def X := SingleStepDefectBound`
  alias), F=1, D=0, guard=5. The one `SingleStepDefectBound` string in the file is in the
  honest-scope comment, not an alias.

## `#print axioms` (all load-bearing decls)

All of `sqrtSub_leRat_floor`, `leRat_abs_of_two_sided`, `one_add_le_sq`, `one_le_sq`,
`chiBlk_le_sq`, `chiFine_le_sq`, `sqrtChiBlk_sub_sqrtChiFine_le`,
`sqrtChiFine_sub_sqrtChiBlk_le`, **`epsilon_majorant`**, `delta_eq_epsRen`,
`physEps_controlled` report `[propext]` or `[propext, Quot.sound]`. No `sorryAx`, no
`Classical.*`, no `native_decide`.

## Honest verdict

**The ε_k CReal→Q' fidelity gap is CLOSED as a fidelity bridge.** The √-difference bound
is genuinely proved by real constructive-`sqrt` manipulation (Heron lower witness +
order-reflected squaring), not assumed. The character-difference bound is a genuine
per-step `δ≥0` algebraic inequality, not a circular restatement of summability. The
majorant makes the audit's implicit obligation a theorem: the rational surrogate
provably dominates the physical `√χ` leakage, so rational summability now genuinely
controls it.

**It does NOT equi-inhabit `singleStep` (not a C++).** The majorant is orthogonal to
whether the surrogate `bondMovingDeltaRen` decays quadratically/is summable — that is the
untouched `SingleStepDefectBound` obligation. The guard correctly stays 5: no
Clay-frontier type is inhabited; nothing is faked; `Σ ε_k < ∞` is NOT claimed. This is
the intended F-move (a per-step CReal→Q' fidelity bridge), not a summability proof.
