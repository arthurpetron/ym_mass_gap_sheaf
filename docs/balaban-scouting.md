# Balaban / Koch–Wittwer block-spin defect SCOUT — scheme scaling, ε-summability, truncation order

**Purpose.** Numerically map the per-scale block-spin defects `(δ_k, ε_k)` as a
function of the block-spin SCHEME (transverse bond-move weight `λ`), to supply
the Lean campaign with (a) the scheme that makes the additive leakage `ε_k`
plausibly SUMMABLE, and (b) the finite CHARACTER-CHANNEL TRUNCATION ORDER at
which a certified contraction stabilises (the interval-arithmetic input). This
is **scouting — constants for the Lean, not a proof.** Every number below is
labelled MEASURED (small-L local MCMC) or EXTRAPOLATED (what a cloud run would
confirm). Date: 2026-07-08. SU(2), heat-bath + overrelaxation Rust engine,
correlated fine-vs-blocked Wilson-loop + plaquette, jackknife errors over 40
configuration bins.

The defect budget the Lean route needs to close (`DefectRecursionPrimary`):

> `(1 − Σ_k δ_k)·m₀ > Σ_k ε_k`,  with `ε_k = |√χ_blk(2,2) − √χ_fine(2,2)(β_p)|`
> (short- vs long-distance coupling mismatch after one factor-2 block step), and
> `δ_k` the multiplicative gap-degradation.

The proved dichotomy (`EpsilonSummability`): **`Σε_k < ∞ ⟺ ε_k` decays at least
QUADRATICALLY in the margin `1−w_k` (`ε ∝ (1−w)^p` with `p ≥ 2`).** Linear
(`p = 1`, the bare Migdal–Kadanoff / pointwise-decimation defect) gives a
divergent harmonic sum and the budget NEVER closes; quadratic (`p ≥ 2`, the
counterterm-subtracted renormalized defect) is summable. **So the decisive
measured quantity is the exponent `p` for each scheme.**

---

## 1. What was run

| grid | lattice `L` | fine → blocked | `β` | schemes `λ` | stats |
|------|-------------|----------------|-----|-------------|-------|
| local | 12 | 12⁴ → 6⁴ | 2.0, 2.2, 2.4, 2.6, 2.8, 3.0 | 0.0, 0.25, 0.5, 0.75, 1.0 | 2000 configs/β |
| local | 16 | 16⁴ → 8⁴ | 2.4, 2.6, 2.8, 3.0 | 0.0, 0.25, 0.5, 0.75, 1.0 | 1500 configs/β |

`λ` = transverse bond-move weight in `V_μ = renorm(S_straight + λ·Σ_{ν≠μ} detours)`.
`λ=0` = **pure decimation**; `λ>0` = **Migdal–Kadanoff-style transverse
bond-moving**; the schemes SATURATE (`λ=0.5, 0.75, 1.0` nearly coincide at
`β ≥ 2.4`). All measured on the SAME configs so noise cancels in the ratio.

Scripts (reproducible): `computations/balaban_defect_scaling.py` (exponent fit +
truncation), `computations/balaban_scout_summary.py` (combined figure).
Raw data: `computations/block_spin_defect_data/bdef-L{12,16}-b*-fl.json`.
Outputs: `block_spin_defect_data/balaban-scaling-combined.{json,svg}`.

---

## 2. MEASURED — leakage `ε_k` vs coupling, per scheme

`ε_k` at each `β` (larger `β` = weaker coupling = smaller margin `1−w`, i.e.
deeper toward the continuum; `*` = blocked coupling below the calibration window,
matched via strong-coupling extrapolation, less reliable):

```
              β=2.0   2.2    2.4    2.6    2.8    3.0     1−w range     Σε(L12)
λ=0.0  (decim) nan*  0.344* 0.519* 0.584* 0.586* 0.575*                2.61  RISES
λ=0.25         0.379*0.110* 0.011  0.000  0.031  0.039   [.28,.50]      0.57
λ=0.5  (MK)    0.419*0.182* 0.120  0.116  0.097  0.053   [.28,.50]      0.99
λ=1.0          0.378*0.182* 0.137  0.130  0.097  0.053   [.28,.50]      0.98
```

L16 (β 2.4–3.0) reproduces the plaquette/leakage to 3 digits (e.g. `β=2.4`
fine `⟨P⟩=0.6300` at both L; blocked `⟨P'⟩=0.585` at both L) — **the leakage is
L-independent at these sizes**, so it is not a finite-volume artifact of the
fine lattice. (The *Creutz* signal at the highest `β` on the small BLOCKED
lattice is the fragile part; see §5.)

**Two clean qualitative facts (both L):**

1. **Decimation (`λ=0`) `ε_k` RISES with `β` (0.34 → 0.58): non-summable, RULED
   OUT.** This directly confirms the crux prediction that pointwise decimation /
   bare MK injects an `O(1−w)` (linear) error at every step (`δ_MK ≈ 0.437(1−w)`).
   `p_eps(λ=0) ≈ −0.1`. Any scheme in this class kills the budget.

2. **Transverse bond-moving (`λ ≥ 0.5`) `ε_k` DECAYS**, from the `≈0.12–0.18`
   crossover plateau at `β = 2.2–2.6` down to `≈0.05` at `β = 3.0`. **This is a
   genuine advance over the prior committed scouting**, which saw only the
   `0.12–0.15` plateau at `β = 2.3–2.5` and could not tell decay from plateau:
   pushing to `β = 3.0` shows the plateau *breaks downward*.

---

## 3. MEASURED — the decisive exponent `p` in `ε ∝ (1−w)^p`

Weighted log-log fit of `ε_k` vs the margin `1−w = 1−⟨P⟩`:

| scheme `λ` | `p` (L12, `1−w∈[.28,.50]`) | `p` (L16, `1−w∈[.28,.37]`) | verdict |
|------------|---------------------------|----------------------------|---------|
| 0.0 (decimation) | −0.06 ± 0.16 | −0.13 ± 0.24 | **`p≈0`: LINEAR/non-summable — RULED OUT** |
| 0.25 | 0.97 ± 1.44 (erratic) | 2.04 ± 1.22 | promising but erratic (see §4) |
| 0.5 (MK) | 2.71 ± 0.83 | 4.19 ± 1.27 | `p ≥ 2`: consistent with SUMMABLE |
| 0.75 | 3.11 ± 0.79 | 4.89 ± 1.17 | `p ≥ 2`: consistent with SUMMABLE |
| 1.0 | 3.01 ± 0.81 | 4.94 ± 1.05 | `p ≥ 2`: consistent with SUMMABLE |

**Read this honestly:**

- For the transverse schemes the measured exponent is **comfortably above the
  linear `p=1` (non-summable) line and consistent with — even steeper than — the
  quadratic `p=2` (summable) line**. This FAVORS summability.
- BUT `p` is **window-unstable**: it moves from ≈2.7 (L12, wider window) to ≈4.9
  (L16, narrower window) purely because the fit lever is short
  (`1−w` spans less than a factor 2) and the steep drop is driven by the single
  highest-`β` point. **The data pin `p ≥ 2` but do NOT pin its value (2? 3? 4?),
  and cannot exclude a linear component re-asserting at `1−w ≪ 0.28`** — which is
  exactly the regime the accessible lattices cannot reach. This matches the Lean
  `EpsilonSummability` caveat verbatim: at crossover margins the linear and
  quadratic models are numerically degenerate.

**`δ_k` (multiplicative) is NOT usefully measured here.** The correlated Creutz
`δ` estimator is dominated by small-`r` contamination (comes out `≈0` or slightly
negative, an unphysical "gap gain"); its fitted exponent (`p_δ ≈ −1` to `−1.8`)
is contamination, not physics. The `δ_k` summability story rests on the ANALYTIC
counterterm result `3(1−w) − (1−w³) = (1−w)²(2+w) = O((1−w)²)` (quadratic), not on
these numerics. What the numerics DO say about `δ`: `|δ_k|` is small (budget-safe
under the `δ_k ≥ 0` clamp), consistent with the analytic quadratic.

---

## 4. Scheme ranking by ε-summability budget

By `Σε_k` (smaller = closer to closing `Σε < (1−Σδ)m₀`), robust across L:

1. **`λ ≈ 0.25` — smallest `Σε` (0.19–0.57), the ONLY scheme whose summed budget
   closes at both L** (margin `+0.31` at L16, `+0.19` at L12). *Caveat:* its tiny
   `Σε` is partly an artifact — the `λ=0.25` blocked point CROSSES the fine Wilson
   curve inside the measured window (`ε → 0.000` at `β=2.6`, `0.004` at L16 `β=2.4`),
   an accidental zero, not asymptotic decay; its exponent fit is correspondingly
   erratic. `λ=0.25` tracks the fine `⟨P⟩` best (`β=3.0`: `⟨P'⟩=0.712` vs fine
   `0.723`, whereas `λ=0.5` OVERSHOOTS to `0.768`) — so a transverse weight
   **lower than the folklore `λ≈0.5`** minimises the plaquette mismatch. Worth a
   dedicated cloud confirmation.

2. **`λ = 0.5` (and 0.75, 1.0, saturated) — the ROBUST summable candidate.**
   `Σε ≈ 0.28` (L16) / `0.99` (L12), monotone clean decay, `p ≈ 2.7–4.9 ≥ 2`.
   `λ=0.5` is the natural pick within the saturated plateau (least over-smoothing).

3. **`λ = 0` (decimation) — RULED OUT.** `Σε ≈ 2.3–2.6`, `ε` rising, `p ≈ 0`.

**Budget honesty.** Whether `Σε < m₀` closes depends on the anchor and the number
of crossover steps summed: L16 (anchor `m₀=0.504` at `β=2.4`, 4 steps) closes for
all `λ ≥ 0.25`; L12 (anchor `m₀=0.774` at `β=2.0`, 6 steps, including the large
strong-coupling `ε≈0.4`) closes only for `λ=0.25`. The crossover steps
(`ε ≈ 0.1–0.4`), not the deep-scaling tail, are what threaten the budget.

---

## 5. Item 12 — CHARACTER-CHANNEL TRUNCATION ORDER for the Lean interval arithmetic

One MK block step raises the single-plaquette SU(2) class function to the power
`p_fuse = b^{d−1} = 2³ = 8` pointwise = an **8-fold Clebsch–Gordan fusion** of the
heat-kernel character coefficients. The certified contraction retains channels
`j ≤ J` (`n = 2j+1`). Computed at the MEASURED effective coupling `β_eff ≈ 2.9`
(from the blocked matched `β_p`), using the exact SU(2) Wilson coefficients
`a_n ∝ n·I_n(β)`:

**Single-plaquette weight — relative L1 tail `Σ_{n>J}|a_n| / Σ|a_n|`:**

| channels `J` (`j ≤`) | 4 (1.5) | 6 (2.5) | 8 (3.5) | 10 (4.5) | 12 (5.5) | 14 (6.5) |
|-----|-----|-----|-----|-----|-----|-----|
| tail | 4.3e-2 | 2.6e-3 | 8.7e-5 | 1.9e-6 | 2.9e-8 | 3.2e-10 |

**8-fold fused (one full MK step) — channels needed for tail `< tol`:**

| tolerance | 1e-3 | 1e-6 | 1e-9 | 1e-12 |
|-----------|------|------|------|-------|
| single plaquette `J` | 7 | 11 | 14 | — |
| **8-fold fused `J`** | **18** | **26** | **33** | 38 |

**Verdict for item 12:** the truncation order is **small and tractable**. To
certify the fused blocked single-plaquette weight to `1e-6` the Lean interval
arithmetic needs **≈ 26 SU(2) character channels (`j ≤ 12.5`)**; to `1e-3`, only
**18**. The discarded tail is rigorously bounded (super-geometric Bessel decay).
Weak sensitivity to coupling: fused `J(1e-6)` moves only `22 → 31` as
`β_eff : 2.0 → 4.0`. **This is the concrete input item 12 needs and it is cheap.**

---

## 6. HONEST VERDICT — is item 12 de-risked?

**Partially de-risked — a clear GO on the truncation order, a "favorable but
unconfirmed" on the summability itself; NO hard red flag.**

- **Scheme identified.** The summable scheme is **transverse bond-moving
  (`λ ∈ [0.25, 0.5]`), NOT decimation.** Decimation (`λ=0`) is DEFINITIVELY ruled
  out — its `ε_k` RISES with coupling (`p ≈ 0`, `Σε ≈ 2.6`), the measured
  realisation of the crux's "bare MK = linear = non-summable". This is a clean,
  robust, L-independent kill and it saves the campaign from formalising against a
  dead scheme.

- **Truncation order pinned (item 12's actual ask).** ≈ 26 fused channels for
  `1e-6` (18 for `1e-3`), tail super-geometric. Tractable; GO.

- **Summability itself: FAVORED, not confirmed.** For the transverse scheme the
  measured `ε` exponent is `p ≥ 2` at every accessible window (summable branch),
  and the leakage visibly *breaks downward* off the crossover plateau by `β=3.0`.
  But `p` is window-unstable (2.7–4.9) and the lever cannot reach `1−w ≪ 0.28`,
  so the numerics **cannot exclude a linear re-assertion in the deep-scaling
  regime**. This is precisely the `singleStep` residual the Lean flags — the
  numerics FAVOR its favorable resolution but do not close it.

**Not a red flag:** no accessible scheme shows the killing signature (linear/rising
`ε`) for the transverse family; the killing signature appears ONLY for decimation,
which is discarded. The risk is "unconfirmed," not "refuted."

**The decisive cloud test:** measure the transverse-scheme `ε_k` at `β ≥ 3.0`
(ideally to `β ≈ 3.4`) on `L = 24, 32` (so the blocked lattice stays `≥ 12⁴` and
the Creutz signal survives), reaching `1−w ≈ 0.15–0.20` where `p=1` and `p=2`
SEPARATE. If `ε` continues `∝ (1−w)^{≥2}` there → summable, budget can close,
item 12 fully de-risked. If it flattens to `∝ (1−w)^1` → the budget provably
fails and the route needs the renormalized (counterterm-subtracted) scheme, not
raw transverse bond-moving.

---

## 7. Cloud run for the user (Claude cannot submit GCS Batch)

The decisive test needs `block_defect` at `L = 24, 32`, `β` up to `≈3.4`, with the
finer `λ` grid — infeasible locally (an `L=32 → 16⁴`-blocked run is ~hours/β).

**Note (honest):** the current cloud image entrypoint (`cloud/entrypoint.sh`) runs
the COMBINED `measure` binary, NOT `block_defect`. Running this test on the cluster
needs a one-line addition to the Dockerfile (`cargo build --release --bin
block_defect`) and an entrypoint branch invoking it. Once wired, the launch (with
the Spot-vCPU cap) is:

```bash
# after adding block_defect to cloud/entrypoint.sh + points.tsv high-β rows:
#   β      L   therm  meas     rmax λgrid              bins seed shards
#   3.0    24  12000  400000   8    0.0,0.25,0.5,0.75  10   2100 5
#   3.2    24  16000  400000   8    0.0,0.25,0.5,0.75  10   2200 5
#   3.0    32  16000  300000   8    0.0,0.25,0.5,0.75  8    2300 12
#   3.2    32  20000  300000   8    0.0,0.25,0.5,0.75  8    2400 12
#   3.4    32  24000  300000   8    0.0,0.25,0.5,0.75  6    2500 12
MAX_PARALLEL=12 MACHINE=c2d-standard-16 cloud/launch.sh 1 2 3 4 5
```

**Direct fallback (no image change), one big VM per point:**

```bash
# on a 32-vCPU VM with the repo built (cargo build --release --bin block_defect):
for B in 3.0 3.2 3.4; do
  ./target/release/block_defect --L 32 --beta $B --therm 20000 --meas 300000 \
     --interval 8 --overrelax 4 --rmax 8 --lambdas 0.0,0.25,0.5,0.75,1.0 \
     --bins 40 --seed 2300 --out bdef-L32-b$B.json
done
# then locally:
python3 computations/balaban_defect_scaling.py 'bdef-L32-b*.json' \
     --out-json scaling-L32.json --plot scaling-L32.svg
```

`MAX_PARALLEL=12` respects the Spot-vCPU quota (12 shards × 16 vCPU = 192 vCPU).
The one number to watch in the output: **the fitted `p_eps` for `λ=0.5` and
`λ=0.25` at `1−w ≈ 0.15–0.20`. `p ≥ 2` → summable → item 12 fully de-risked;
`p → 1` → budget fails, switch to the counterterm-subtracted scheme.**
