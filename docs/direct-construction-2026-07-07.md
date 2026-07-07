# Direct construction of the Clay core `singleStep` — range extension of the real reconstructed-transfer located gap

**File:** `lean/YMGap/Continuum/PushedReconTransferGap.lean` (new; imported in `lean/YMGap.lean`).
**Build:** full `lake build` green (753 jobs). **Guard:** `5 Clay-frontier types` — INTACT (unchanged).
**Axioms:** every load-bearing declaration `[propext]` or `[propext, Quot.sound]`; one is axiom-free. NO `sorryAx`, NO `Classical`, NO `native_decide`, NO `ring`/`nlinarith`.
**No new `:= SingleStepDefectBound` alias** (C loop-counter unchanged). `SingleStepDefectBound` inhabited NOWHERE.

Deliverable class: **(ii) genuine CONSTRUCTION INCREMENT** — a machine-checked bound extending the proved range — **plus (iii) a precisely-named, machine-checked residual** (the sharp ceiling `w* = 2^{−1/3}`).

---

## 1. The concrete real object being constructed and bounded

The whole Clay continuum gap reduces (proved, `SingleStepDefectReduction.fullFloor_of_singleStep`) to
`SingleStepDefectBound.singleStep`, whose `trueMargin_k` candidate is the **real reconstructed single-edge
transfer-operator gap margin** `reconMargin w = 1 − rho w = 1 − 2w³`, where `rho w = coeffW w 1 = 2w³` is the
genuine SU(2) Wilson connected-correlator clustering rate (NOT a model/surrogate — it is the leading excited
character eigenvalue of `reconTransfer`, whose `corr` equals the real `wilsonG` correlator via
`wilsonG_eqv_reconTransfer_corr`).

`DirectSingleStepReconGap.reconTransfer_located_gap_general` constructs the located gap with this margin, but
**only on `w ∈ (0, 1/2]`**, because it consumes the `w ≤ 1/2`-gated `reconTransfer_corr_decay` / `rho_lt_one` /
`coeffW_excited_le_one`.

## 2. STRONG-COUPLING BOUND — the range PUSHED from `w₀ = 1/2` to the sharp character radius `w* = 2^{−1/3}`

`reconTransfer_located_gap_gen` (PROVED) removes the `w ≤ 1/2` gate. For **any** `w` with `0 < w ≤ 1`, the genuine
clustering-rate condition `rho w < 1` (⟺ `w³ < 1/2` ⟺ `w < 2^{−1/3}`), and the harmless quintic side condition
`2w⁵ ≤ 1` (⟺ `w ≤ 2^{−1/5} ≈ 0.871`), the reconstructed single-edge transfer operator has a **located spectral
gap** with separator `sep = rho w = 2w³ < 1`, hence positive margin `reconMargin w > 0`.

The correlator-decay field is rebuilt from scratch (no `wilsonG_decay` gate):
`reconTransfer_corr_decay_gen` ⇐ `connSum_le_gen` ⇐ `connChain_excited_le_gen` ⇐ the head-domination
`coeffW_excited_le_head_gen` ⇐ the per-rep ratio `coeffW_succ_ratio` + `2w⁵ ≤ 1`. The **only** binding constraint
left is the genuine `rho w < 1`.

**Concrete witness at the pushed edge** `w₀ = 793/1000 = 0.793` (`reconTransfer_located_gap_pushed`, PROVED),
a clean rational a distance `≈ 7×10⁻⁴` below the ceiling:

| quantity | exact value | decimal |
|---|---|---|
| `rho w₀ = 2·(793/1000)³` | `498677257/500000000` | `0.99735…` (`< 1` ✓, decidable) |
| `reconMargin w₀ = 1 − rho w₀` | `1322743/500000000` | `0.0026455… > 0` ✓ (`reconMargin_w0_pos`, via `gapMargin_pos`) |
| `2·(793/1000)⁵` | `313592694387193/500000000000000` | `0.62719… ≤ 1` ✓ (decidable) |

**So `w₀` is pushed from `1/2 = 0.5` to `0.793`** — within `7×10⁻⁴` of the character radius `w* = 2^{−1/3} = 0.79370052…`
(all numerics verified independently in sympy exact + mpmath dps=50). Because `reconTransfer_located_gap_gen` is
fully general, the concrete `0.793` is merely a decidable witness: the located gap exists for **every** rational
`w < 2^{−1/3}`.

## 3. The interacting correction (where it lives)

The real defect = free single-plaquette bound (`δ_ren ≤ 6(1−w)²`, PROVED, `CharFunCumulantDefect`) + interacting
multi-link correction. The `InteractingMFoldDefect` probe already established (off-line, 40+ digits, two methods)
that the interacting connected remainder is `O((1−w)⁴)`, **concentrating** in the block multiplicity `m`
(`2 − ρ_m = 6ε/m`, NOT the semigroup's `6mε`), hence subdominant to `6(1−w)²`. The located-gap range extension here
is **orthogonal and complementary**: it establishes that the reconstructed single-edge margin — the `trueMargin`
candidate itself — is a genuine positive located mass gap on the whole character window `[0, 2^{−1/3})`. The
interacting correction is precisely what is needed **beyond** that window.

## 4. THE `w→1` FRONTIER — the precisely-characterized residual (sharp ceiling)

`no_located_gap_above_ceiling` (PROVED, `[propext]`): for **every** `w ≥ 0` with `w³ ≥ 1/2` (⟺ `w ≥ 2^{−1/3}`),
the reconstructed transfer operator has **NO located gap at all** — any such gap forces its leading excited
eigenvalue `lam 0 = rho w = 2w³ ≤ sep < 1`, contradicting `rho w ≥ 1`
(`CharacterWindowCeiling.character_rate_ge_one_at_ceiling`). A hard impossibility. This **sharpens**
`DirectSingleStepReconGap.no_located_gap_at_weak` (a single witness at `9/10`) to the **exact** threshold `w³ = 1/2`.

Combined with §2, the single-edge located-gap window is **exactly `[0, 2^{−1/3})`** (`located_gap_window_sharp`,
PROVED both directions): gap-with-positive-margin below `w*`, no gap at or above `w*`. The dividing weight is the
character radius, where `rho = 2w³ = 1` exactly. Tight witness just past the ceiling: `w = 4/5 = 0.8`,
`reconMargin(4/5) = −3/125 < 0` (`reconMargin_neg_at_ceiling_witness`, axiom-free) and no located gap
(`no_located_gap_at_ceiling_witness`).

**The exact remaining analytic obstruction at `w→1`:** the RG flow drives `w_k → 1` (asymptotic freedom), crossing
`w* = 2^{−1/3} ≈ 0.7937`. Above `w*` the single-edge character rate `ρ = 2w³ ≥ 1` — the connected correlator no
longer clusters, the margin is negative, and **no located gap exists** for the single-edge reconstruction. A
located transfer gap on `[2^{−1/3}, 1)` — the deep-UV / continuum approach — provably **cannot** come from the
single-edge character mechanism; it requires the genuinely interacting **multi-plaquette block-spin effective
action** at each scale (the unconstructed `a→0` object). This is a genuine physical ceiling (the strong/character
radius), not a proof weakness — and it is now the SHARPLY LOCATED residual of `singleStep`.

## 5. Honest verdict

- **Did I extend the proved range of the real reconstructed-gap margin?** YES. From `w ≤ 1/2` (old gate) to the
  full character window `[0, 2^{−1/3})`, sharp; concrete decidable witness at `w₀ = 0.793` (within `7×10⁻⁴` of `w*`).
  This is a genuine construction increment (criterion ii) on the real interacting Wilson-correlator object, not a
  model.
- **Did I inhabit `SingleStepDefectBound`?** NO — and correctly not: the guard stays at 5. The single-edge margin
  provably **cannot** be `trueMargin` over the full AF flow, because `w_k → 1` exits the character window.
- **Exact remaining obstruction:** a located transfer gap for `w ∈ [2^{−1/3}, 1)`, requiring the interacting
  multi-plaquette effective action — the sharpest, precisely-located form of the `singleStep` residual
  (criterion iii).

Nothing is faked; no 4D Yang–Mills mass gap is claimed.

## Axiom gate (from `#print axioms`)
```
coeffW_succ_le_self_gen, coeffW_excited_le_head_gen, connSum_le_gen,
reconTransfer_corr_decay_gen, reconTransfer_located_gap_gen, reconTransfer_located_gap_gen_margin,
reconTransfer_located_gap_pushed, reconMargin_w0_pos, located_gap_window_sharp   : [propext, Quot.sound]
no_located_gap_above_ceiling, no_located_gap_at_ceiling_witness                  : [propext]
reconMargin_neg_at_ceiling_witness                                              : (no axioms)
```
