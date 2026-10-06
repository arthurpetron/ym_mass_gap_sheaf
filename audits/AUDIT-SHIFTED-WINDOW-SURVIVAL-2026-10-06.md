# AUDIT: shifted H1 from backward-window survival; fieldspace g² convention fix (2026-10-06)

File: `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean` (375 lines,
SHA-256 `1a379fb25388dcfae32474b85b620e4934a0c19f402ec2b67604d960ece30077`).
Imports `YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor` only. Root-registered in
`lean/YMGap.lean` directly after `BF4WilsonAllNomeShiftedH1Anchor`.

## 1. Increment

Reduces the OPEN shifted H1 (`PathShiftedEpsBound`, from
`AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md`) to a pure moment statement,
BACKWARD-WINDOW SURVIVAL `θ R_j(side_j/2) ≤ R_j(side_j+1)`, through a
constructive moment-only compiler. It uses no spectral measure, no exp/log and
only rational constants.

## 2. Direction check (the proposed forward reduction is wrong; the parent's correction is right)

Write `q_k = R(k+1)/R(k)`. Log-convexity `R(k+1)^2 ≤ R(k)R(k+2)` makes `q_k`
nondecreasing, and contraction gives `q_k ≤ 1`.

* FORWARD: `R(2s)/R(s) = Π_{k=s}^{2s-1} q_k ≥ q_s^s` is an UPPER bound on `q_s`.
  Moreover every factor is `≤ 1`, so `R(2s)/R(s) ≤ q_s`. Hence forward survival
  `R(2s) ≥ θ R(s)` gives only `1 - q_s ≤ 1 - θ`, an O(1) eps bound with no `1/s`.
  **Counterexample** (Hausdorff moment sequence, atoms `λ = 1` with weight 1 and
  `λ = 1/2` with weight `2^s`): `R(n) = 1 + 2^(s-n)`. Then `R(s) = 2`, `R(s+1) = 3/2`
  and `R(2s) = 1 + 2^-s ≥ R(s)/2` (θ = 1/2), but `s(R(s) - R(s+1))/R(s) = s/4 → ∞`.
  With the strict contraction `λ1 = 1 - 1/s^2` in place of 1: at s = 40, the
  forward ratio is 0.48 and `s·eps_s` is 10.1 (python check). So no uniform c0 exists.
  (Its backward window `R(s+1)/R(s/2)` is ≈ 1.4e-6, consistent with §3.)
* BACKWARD: for `p ≤ s`, `R(s+1)/R(p) = Π_{k=p}^{s} q_k ≤ q_s^(s-p+1)`, a LOWER
  bound on `q_s`. This is the right direction.
* Refinement: log-convexity is not needed. CONVEXITY of `R` (the energy
  `e(k) = R(k) - R(k+1)` is nonincreasing) already gives
  `R(p) - R(s+1) = Σ_{k=p}^{s} e(k) ≥ (s-p+1) e(s)`. Then `θ R(p) ≤ R(s+1)` gives
  `θ (s-p+1) e(s) ≤ (1-θ) R(s+1) ≤ (1-θ) R(s)`, i.e.
  `(s-p+1)(1-q_s) ≤ (1-θ)/θ`. This is the same constant that Bernoulli gives from
  `q_s^L ≥ θ` (since `(1-x)^L ≤ 1/(1+Lx)`). Log-convexity would sharpen
  `(1-θ)/θ` to `-log θ`; not formalized. On the carrier, convexity is exactly
  `m(k,2) = B(x, T^k (I-T)^2 x) ≥ 0` (`mixedMoment_nonnegative`) combined with
  the exact split `m(k,l) = m(k+1,l) + m(k,l+1)` (`mixedMoment_split`). The
  even/odd Jensen lemmas are not needed.
* Window choice: `p = side/2`, `n = side - side/2`, `L = n + 1 ≥ side/2`, so
  `c0 = 2(1-θ)/θ`. Taking `p = 0` would require unshifted survival
  `θ R(0) ≤ R(side+1)` (`PathLagSurvival`). That is stronger and heuristically
  FALSE for the box-smoothed state (§5).

## 3. Declaration table

| line | declaration | content |
|---|---|---|
| 211 | `window_energy_antitone x n k` | `e(k+n) ≤ e(k)`, `e(k) = mixedMoment x k 1` |
| 223 | `window_telescope x n p` | `R(p+n+1) + (n+1)·e(p+n) ≤ R(p)` |
| 241 | `window_energy_bound` | `θR(p) ≤ R(p+n+1)`, `0≤θ≤1` ⟹ `θ(n+1)e(p+n) ≤ (1-θ)R(p+n)` |
| 268 | `window_epsBound` | cleared H1 shape at lag `s = p+n` (below) |
| 293 | `oneStepEpsBound_one` | `L = 1`: `1 ≤ c0` ⟹ `OneStepEpsBound x 1 c0` (used for j = 0) |
| 313 | `PathShiftedWindowSurvival tr θ` | **OPEN** reduced Prop |
| 318 | `PathLagSurvival tr θ` | unshifted p = 0 survival (stronger; heuristically false) |
| 322 | `pathShiftedWindowSurvival_of_lagSurvival` | p = 0 survival ⟹ window survival |
| 332 | `pathShiftedEpsBound_of_windowSurvival` | **compiler, path form** |
| 353 | `path_normalized_anchor_of_windowSurvival` | **A03 package from window survival** |

Exact statements:

```lean
theorem window_epsBound (x : V) (p n s L : Nat) (hpn : p + n = s) (theta c0 : Q')
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc : Q'.ofNat L * (1 + -theta) ≤ theta * Q'.ofNat (n+1) * c0)
    (hsurv : RCle (RCscale theta (MM x p 0)) (MM x (s+1) 0)) :
    RCle (RCscale (Q'.ofNat L) (RCsub (MM x s 0) (MM x (s+1) 0)))
      (RCscale c0 (MM x s 0))
-- MM = mixedMoment hw0 hw1; MM x k 0 = B(x, T^k x) definitionally.

def PathShiftedWindowSurvival (tr : DyadicSmoothedTrajectory) (theta : Q') : Prop :=
  ∀ j, 1 ≤ j → RCle (RCscale theta (tr.response j (side j / 2))) (tr.response j (side j + 1))

theorem pathShiftedEpsBound_of_windowSurvival (tr : DyadicSmoothedTrajectory) (c0 theta : Q')
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (Hw : PathShiftedWindowSurvival tr theta) : PathShiftedEpsBound tr c0

theorem path_normalized_anchor_of_windowSurvival (tr : DyadicSmoothedTrajectory)
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : (0 : Q') < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : (1 : Q') ≤ c0)
    (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hcd : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (Hw : PathShiftedWindowSurvival tr theta) (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl
```

`hc1 : 1 ≤ c0` covers only `j = 0` (side 1, no shift), where the trivial bound
`E ≤ B` is used. It is automatic when `θ ≤ 2/3` and `c0 = 2(1-θ)/θ`. For `j ≥ 1`
the compiler uses `pathShiftedEpsBound_iff_response` with `x = Y_j`,
`p = side_j/2`, `n = side_j - side_j/2` and `L = side_j ≤ 2(n+1)`.
Example: θ = 1/10 allows c0 = 18.

## 4. Open inputs after this increment

`PathShiftedWindowSurvival tr θ` (uniform, the single quantitative input) and
`PathShiftedNondegenerate tr fl` (qualitative, per scale). Neither is proved.
`PathLagSurvival` is recorded as a stronger sufficient condition that is
heuristically false for the box-smoothed state.

## 5. Does the reduced Prop match the numerics? (honest assessment)

**Monte Carlo** (`AUDIT-ROUTE-REPOINT-DIRECT-RESPONSE-2026-10-05.md`, bundle
`computations/ym_direct_response_mc_2026_10_05/`): the "survival ≈ 0.10, flat"
is `R(s)/R(0)` at lag `s = side`, i.e. UNSHIFTED (p = 0) survival. It is measured
for the APE-20 spatially smeared ZERO-MOMENTUM `s×s` Wilson-loop correlator with
no time smoothing. The run is SU(2) on 16^4 at (β,s) = (2.4,2), (2.5,3), (2.6,4),
with values 0.104 ± 0.005, 0.101 ± 0.006 and 0.110 ± 0.008. The same table's
forward ratio `R(2s)/R(s)` = 0.13 to 0.34 is irrelevant by §2.

* Relation (paper argument; uses log-convexity of the measured correlator, which
  holds for a reflection-positive transfer matrix): for `s ≥ 2` and `p = ⌊s/2⌋`,
  `R(s+1)/R(p) ≥ R(s+1-p)/R(0) ≥ R(s)/R(0)`. So the measured p = 0 survival
  IMPLIES backward-window survival with the same θ ≈ 0.10 for THAT state. The
  reduced Prop is weaker than what was measured.
* Mismatch:
  * The measured state is not the Lean anchor state: `Y_j` is the box
    time-smoothed plaquette-family coherent state, `M_j = m·side_j`, with no
    spatial smearing.
  * Only 3 scales were run, smearing is fixed in lattice units, and lag 8 wraps
    on L = 16.
  * No Monte Carlo has measured `R_Y(side+1)/R_Y(side/2)` for the actual `Y_j`.
* **Free-field heuristic for the actual box-smoothed `Y`** (`/workspace/p10/win.py`):
  spectral weight `ρ ∝ √(E-2μa) E^3`, `M = side`, side = 16 to 1024, `L = side·a·μ`.
  * Unshifted survival `R(s+1)/R(0)` goes to 0, roughly like `side^(-2.5)`; for
    example 6.5e-6 at s = 16 and 1.9e-10 at s = 1024 (L = 0.25). So
    `PathLagSurvival` is heuristically false.
  * Backward-window survival `R(s+1)/R(s/2)` is FLAT in side at fixed `L`:
    0.13 (L = 0.25), 0.087 (L = 1) and 0.0055 (L = 4) at s = 1024. It decays with
    physical size, so heuristically it holds uniformly only with `L_j` bounded
    (AF-calibrated schedule, `NomeSchedulePhysicalBox`).
  * The compiler is lossy: the constant it gives, `2(1-θ)/θ`, is 13 to 21 at L ≤ 1,
    while the true shifted `eps·side` is 3 to 4.
* Verdict: the reduced Prop is heuristically plausible under an AF-calibrated
  schedule and is implied by the kind of p = 0 survival the Monte Carlo measured,
  but it is unmeasured for the actual Lean state and still OPEN.

## 6. Docs

* `docs/fieldspace-2026-07-06.md:29-30`: the note's own convention `w = e^{-t}`
  (and its bracket and table) is kept, and the line now states the carrier
  convention: per-Casimir weight `w = e^{-t/4}` (`RGTransport.lean:45`), so on
  the carrier `g² = t = −4 log w` and `4(1−w) ≤ g² ≤ 4(1−w)/w` (2026-10-06: `t` is
  only the repo's label for `g²`; the standard coupling is `g² = 2t = −8 log w`,
  see the convention box in `AUDIT-AF-PADDED-TRAJECTORY-2026-10-06.md`). This was flagged
  in `AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md` §5.
* Frontier paragraphs prepended in `docs/PROJECT-STATUS.md`, `lean/README.md`
  and `work_plan.md`: shifted H1 is now reduced to backward-window survival
  (OPEN, heuristic support only). Ledger entry and root import added.

## 7. Verification

* Runs via `~/ymlean_prover_scratch/run_monitored_check.sh`
  (`safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`; guard + snapshot +
  10 s sampler; abort at pressure ≥ 2 or avail < 8192 MiB):
  * p10a 03:28 PT: 3 errors (`rw` with type ascription, missing section args),
    fixed. Peak load1 8.49, pressure 1, min avail 29868 MiB.
  * p10b 03:29 PT: clean. Peak load1 7.49, pressure 1, min avail 26983 MiB.
  * p10final 03:30 PT with `--check-output .../BF4WilsonAllNomeShiftedWindowSurvival.olean`:
    exit 0, 0 errors, 0 sorryAx. Peak load1 7.63, pressure 1, min avail 28447 MiB.
    Log: `~/ymlean_prover_scratch/logs/check-p10final-20261006-033044.out`.
* `python3 scripts/lean_forbidden_token_scan.py` (after root registration):
  `executable_forbidden_hits 0`.
* `#print axioms`: all 10 gates print `[propext, Quot.sound]`; no `sorryAx`.
