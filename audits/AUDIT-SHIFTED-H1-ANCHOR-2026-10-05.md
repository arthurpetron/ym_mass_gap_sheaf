# AUDIT: shifted H1 anchor, shifted telescope, AF-calibrated schedule Props (2026-10-05)

File: `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedH1Anchor.lean` (716 lines,
SHA-256 `1b73448802ef55cf307447b3f39ee62a51162395735b41ddbe71733353629567`).
Imports `YMGap.Continuum.BF4WilsonAllNomeH1FixedScale` only. Root-registered in
`lean/YMGap.lean` directly after `BF4WilsonAllNomeH1FixedScale`.
Namespace `YMGap.Continuum.BF4WilsonAllNomeShiftedH1Anchor`.

## 1. Increment

Follow-up to `AUDIT-H1-FIXED-SCALE-2026-10-05.md`. That audit (and its math note)
argued that the UNSHIFTED box-kernel H1 (`PathEpsBound`) and H2
(`PathFamilyRadiusSurvival`) are heuristically false (free-field spectral weight
rho ~ E^4 puts the Fejer energy at eps ~ 0.95 = O(1), whereas eps ~ c/side is
needed), and that a time shift by `T^(side)` brings the free-field value to
eps ~ 1.9/side. This increment:

1. restates H1 for the time-shifted anchor `x_j = T^(side_j/2) Y_j`
   (`PathShiftedEpsBound`);
2. proves the exact shifted Fejer telescope and its unconditional bound
   `(M+1) E(T^h Y_M) <= R_x(2h)` (the analogue of `smoothedEnergy_le_familyNorm`);
3. feeds the shifted H1 through the existing `NormalizedAnchorData` consumer to
   get `path_normalized_anchor_shifted` (full A03 package at every `j >= a >= 1`);
4. states the AF-calibrated schedule requirement as precise Props over
   `NomeSchedule` and records the repo's actual `1-w <-> g^2` constant.

## 2. Kernel choice: time shift `T^(side_j/2)`, not a new smooth kernel

Chosen: `x_j = T^(h_j) Y_j`, `h_j = side_j/2` (exact for `j >= 1`, `side j = 2^j`).

* **Spectral suppression.** On the spectral side `T^h` multiplies the spectral
  measure by `e^(-2hE)`; with `2h = side` this damps exactly the UV modes
  `E >> 1/side` that make the unshifted box-kernel eps O(1) (box Fejer weight
  decays only like `(M E)^-2`, too slow against free-field `rho ~ E^4`).
  Free-field numerics (`/workspace/p8/spec2.py`, see H1 audit) give
  `eps*side ~ 1.9` for the shift. A smooth kernel (e.g. Gaussian in `n` of width
  ~ side) damps like `e^(-(side E)^2)`, even faster, and heuristically also gives
  `eps = O(1/side)`; since `rho` grows only polynomially, exponential damping
  already suffices, so the smooth kernel gains at most constants, not the
  `1/side` order.
* **Ease in the (B,T) algebra.** `T^s` is self-adjoint and PSD on the completed
  carrier (`completedInner_time_sum`, `completedTime_add`), so
  `B(T^h Y, T^n T^h Y) = R_Y(n+2h)` (`shift_response_pin`) and
  `B(T^h Y, T^h Y) = R_Y(2h)` (`shift_norm_pin`). The shifted response is a pure
  lag shift of the EXISTING `smoothedResponse`; no new orbit sum, kernel mass,
  or Cauchy representative is needed. A smooth kernel would need a new
  `ResponseKernel`, its mass/normalization lemmas, positivity, a new orbit
  vector, and new norm/QCauchy data.
* **Compatibility with `NormalizedAnchorData`.** Checked: the port is nearly
  free. The existing `smoothedAnchorData` (base `Y_j`, block `side_j`,
  normalized state `alpha T^(side_j) Y_j`) is reused verbatim
  (`shiftedPathAnchor` only changes the floor to `kappa*fl_j`). Its
  `MacroRatio` is `kappa R_j(side_j) <= R_j(2 side_j)`. Applying the existing
  `block_survival_of_oneStep_energy` to `x_j` with the shifted H1 gives
  `kappa B(x,x) <= B(x, T^(side) x)`, and the two pins rewrite this to exactly
  `kappa R_j(side_j) <= R_j(side_j + 2 h_j) = R_j(2 side_j)`
  (`path_shifted_macroRatio`). The anchor norm `R_j(2 side_j)` and its Cauchy
  data are unchanged.

## 3. Declaration table

| line | declaration | kind / content |
|---|---|---|
| 235 | `OneStepEpsBound x L c0` | def Prop: `L (B(x,x) - B(x,Tx)) <= c0 B(x,x)` |
| 239 | `shift_norm_pin` | `B(T^h x, T^h x) = B(x, T^(2h) x)` |
| 244 | `shift_response_pin` | `B(T^h x, T^n T^h x) = B(x, T^(n+2h) x)` |
| 267 | `overlap_expand` | `B(T^a x0, T^b Y_M) = sum_k r B(x0, T^(k+a+b) x0)` |
| 282 | `shifted_energy_telescope` | exact: `E(T^h Y_M) = (M+1)^-1 (B(x0,T^(2h)Y_M) - B(T^(M+1)x0, T^(2h)Y_M))` |
| 305 | `shifted_tail_overlap_nonnegative` | tail overlap `>= 0` |
| 315 | `shifted_head_overlap_le` | `B(x0, T^(2h) Y_M) <= R_x(2h)` |
| 332 | `shifted_energy_le_familyResponse` | **shifted telescope bound** `(M+1) E(T^h Y_M) <= R_x(2h)` |
| 350 | `shifted_norm_ge_family_response` | `R_x(2M+2h) <= B(T^h Y_M, T^h Y_M)` |
| 372 | `shiftedEpsBound_of_relativeFloor` | relative floor + `L <= c0 theta (M+1)` => shifted eps bound |
| 396 | `PathShiftedEpsBound tr c0` | **OPEN** shifted H1 |
| 403 | `PathShiftedNondegenerate tr fl` | **OPEN** qualitative, `fl_j <= R_j(side_j)` |
| 407 | `PathShiftedFamilySurvival tr theta` | **OPEN** shifted H2 (optional route) |
| 418 | `pathShiftedEpsBound_iff_response` | `j >= 1`: shifted H1 iff `side_j (R_j(side_j) - R_j(side_j+1)) <= c0 R_j(side_j)` |
| 436 | `pathShiftedEpsBound_of_shiftedFamilySurvival` | shifted H2 + `1 <= c0 theta m` => shifted H1 |
| 468 | `shiftedPathAnchor` | `smoothedAnchorData` at block `side_j`, floor `kappa fl_j` |
| 477 | `path_shifted_macroRatio` | shifted H1 + nondeg => `kappa R_j(side_j) <= R_j(2 side_j)` |
| 521 | `path_shifted_anchor_floor` | `kappa fl_j <= R_j(2 side_j)` (true floor of anchor norm) |
| 550 | `ShiftedAnchorPackage` | def Prop: the 4-part A03 conclusion |
| 581 | `path_normalized_anchor_shifted` | **main**: shifted H1 + nondeg => package |
| 602 | `path_normalized_anchor_shifted_of_survival` | same from shifted H2 |
| 617 | `path_shiftedEps_forces_rate` | screen: `side_j (1 - r_j) <= c0` for any certified Rayleigh rate |
| 650 | `lg2` | `ofNat (Nat.log2 (j+1))` |
| 658 | `NomeScheduleAFCalibrated ns A kappa C` | **OPEN** AF-calibration Prop |
| 667 | `NomeSchedulePhysicalBox ns a Llo Lhi` | **OPEN** physical-box Prop |
| 673 | `dyadicNomeSchedule_margin_side` | `(1 - w_j) side_j ≈ 1/2` for the dyadic interface schedule |

Main theorem, exact hypotheses:

```lean
theorem path_normalized_anchor_shifted (tr : DyadicSmoothedTrajectory) (c0 delta : Q') (a : Nat)
    (ha : 1 ≤ a) (hdelta0 : (0 : Q') ≤ delta) (hdelta : delta < (1 : Q'))
    (hc0 : c0 ≤ Q'.ofNat (side a) * delta) (fl : Nat → Q') (hfl : ∀ j, (0 : Q') < fl j)
    (H1s : PathShiftedEpsBound tr c0) (Hnd : PathShiftedNondegenerate tr fl) :
    ShiftedAnchorPackage tr delta hdelta a fl hfl
```

`ShiftedAnchorPackage`: for every `j >= a`, the normalized anchor
`alpha_j T^(side_j) Y_j` has `B = 1`; block floors `kappa^i <= B(u, T^(i side_j) u)`;
real-time floors `kappa^(i+1)` at represented times with `spacing_j * t <= i`; and
the geometric real-time increment modulus; `kappa = (1-delta)^(2^a)`.

## 4. Open Props (exact text)

```lean
def OneStepEpsBound (x : V) (L : Nat) (c0 : Q') : Prop :=
  RCle (RCscale (Q'.ofNat L) (RCsub (B x x) (B x (T 1 x)))) (RCscale c0 (B x x))

def PathShiftedEpsBound (tr : DyadicSmoothedTrajectory) (c0 : Q') : Prop :=
  ∀ j, OneStepEpsBound (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (trajWidth j)
    (completedTime (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j) (side j / 2)
      (tr.state j)) (side j) c0

def PathShiftedNondegenerate (tr : DyadicSmoothedTrajectory) (fl : Nat → Q') : Prop :=
  ∀ j, RCle (Rq (fl j)) (tr.response j (side j))

def NomeScheduleAFCalibrated (ns : NomeSchedule) (A kappa C : Q') : Prop :=
  (0 : Q') < A ∧ ∀ j : Nat,
    (Q'.ofNat j + kappa * lg2 j + -C) * ((1 : Q') - ns.nome j) ≤ A ∧
    A ≤ (Q'.ofNat j + kappa * lg2 j + C) * ((1 : Q') - ns.nome j)

def NomeSchedulePhysicalBox (ns : NomeSchedule) (a : Q' → Q') (Llo Lhi : Q') : Prop :=
  (0 : Q') < Llo ∧ ∀ j : Nat,
    Llo ≤ Q'.ofNat (side j) * a (ns.nome j) ∧ Q'.ofNat (side j) * a (ns.nome j) ≤ Lhi
```

(`PathShiftedFamilySurvival`, line 407, is an optional alternative route only.)

### Why "from the shifted H1 alone" is impossible, and why `PathShiftedNondegenerate`

If `Y_j` lay in `ker T^(side_j/2)`, then `x_j = 0` and the shifted H1 holds as
`0 <= 0`, yet no unit-norm anchor exists. The shifted eps bound is homogeneous
and cannot by itself give a positive floor. So a QUALITATIVE floor is needed:
`fl_j <= R_j(side_j)` with ANY positive `fl_j`, allowed to depend arbitrarily on
`j` (it only enters `shiftedPathAnchor.floor`, never the constants
`kappa, delta, c0, a`). All UNIFORM content is in the shifted H1. On the actual
carrier `R_j(side_j) = ||T^(side_j/2) Y_j||^2 > 0` is expected (T is injective on
the transfer-matrix side), but it is not proved here; it is a fixed-scale
statement, not a uniform estimate.

## 5. Repo `1 - w <-> g^2` relation and constant

* Carrier coefficient: `def coeffW (w : Q') (s : Nat) : Q' := dimQ s * qpow w (c4 s)`
  (`lean/YMGap/Continuum/BondMovingStep.lean:259`), with
  `def c4 (s : Nat) : Nat := s * (s + 2)` (`lean/YMGap/Continuum/RGTransport.lean:196`).
* Weight: "`w = e^{−t·(1/4)} ∈ Q'`" (`RGTransport.lean:45`); "`E χ_s = dim(s) · w^{C₄(s)}, w = e^{−t/4}`"
  (`lean/YMGap/Continuum/WilsonConsistency.lean:129`, `:137`).
  Heat-kernel character `wilsonCharExp t s = dim e^{-t C2}` (`WilsonFunctional.lean:68`), C4 = 4 C2.
* Coupling: "`1 − e^{−(3/4)t} ≤ g² = t`" (`lean/YMGap/Continuum/NonpertActivityHeatKernel.lean:66`).
* Hence **`g² = t = −4 log w`**, so **`1 − w = g²/4 + O(g⁴)`**, with the exact bracket
  `1 − w ≤ −log w ≤ (1 − w)/w`, i.e. `4(1−w) ≤ g² ≤ 4(1−w)/w`.
* `AFRateCalibration.lean:15` and `:48` state only `1 − w_k ≍ g_k² ≍ 1/k` with no
  constant; `AFRateModulus` (`AFRateCalibration.lean:767`) carries free constants
  `A'/(k+B) <= 1 - w_k <= A/(k+B)`.
* **Inconsistency flagged (not edited):** `docs/fieldspace-2026-07-06.md:30` says
  "`t = −log w`; ... `g² = t = −log w`", i.e. a weight `w = e^{-t}`. That is a
  factor 4 off from the carrier's `w = e^{-t/4}` (per Casimir unit C4). The Lean
  carrier convention is the one used here.
* Heat-kernel vs Wilson action: the repo identifies `g² = t` (heat-kernel
  action). Matching to the Wilson action via Bessel asymptotics (NOT in the repo)
  gives `t ≈ g²/2` at weak coupling, i.e. `g² = −8 log w`; under that convention
  `A` below halves (≈ 1.942). The Prop takes `A` as a parameter either way.

### Two-loop calibration (paper, SU(2))

`b0 = 11/(24 π²)`, `b1 = 17/(96 π⁴)`, `a Λ = (b0 g²)^(-b1/(2b0²)) e^(-1/(2 b0 g²))`.
With `1/g² = u/4 + O(1)`, `u = 1/(1-w)`, bounded `L_j = 2^j a(w_j)` iff
`A u_j = j + κ log₂ j + O(1)`, with
`A = 1/(8 b0 ln 2) = 3.883317…` and `κ = b1/(2 b0²) = 51/121 = 0.421487…`
(python check on the box). Equivalently `1 − w_j ≈ 3.883/j`. The `O(g⁴)` in
`g² = 4(1-w) + O((1-w)²)` shifts `u` by `O(1)`, absorbed in `C`; `lg2 j` is
within 1 of `log₂ j`, also absorbed.

Honest caveat: `A = 1/(8 b0 ln 2)` is irrational, while the Prop's `A : Q'`. A
rational `A ≠ A_phys` with error `ε` makes `L_j` drift like `exp(O(ε j))`; so
`NomeScheduleAFCalibrated` with rational constants is the calibrated SHAPE, and
the exactly physical requirement is `NomeSchedulePhysicalBox` with the true
scale-setting function `a` (supplied, not defined in the repo).

### Relation to `NomeScheduleAFJustified`

`NomeScheduleAFJustified ns := ∃ m : AFRateModulus, ∀ j, m.w j ≈ ns.nome j`
(`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:303`) is the two-sided `1/k`
rate with FREE constants. Paper argument: `NomeScheduleAFCalibrated ns A κ C`
(A > 0) implies it (upper rate from `(j - C)(1-w_j) <= A` for large `j` plus
`1 - w_j < 1` for finitely many `j`; lower rate since `κ log j / j -> 0` and
`1 - w_j > 0`). The converse FAILS: `AFRateModulus` allows `u_j` to vary within
`[(j+B)/A, (j+B)/A']`, an O(j) window, so `L_j` may grow or shrink like
`exp(O(j))`. Hence `NomeScheduleAFJustified` is too weak for bounded `L_j`; the new
Prop is the sharp (log-corrected, pinned-coefficient) version. Neither
implication is formalized here.

### `dyadicNomeSchedule` is NOT AF-calibrated

Proved (`dyadicNomeSchedule_margin_side`): `(1 − w_j) side_j ≈ 1/2`, i.e.
`1 − w_j = 2^-(j+1)`. Paper: for any `A > 0`, `κ`, `C`, the upper constraint
`A <= (j + κ lg2 j + C) 2^-(j+1)` fails for large `j` since the RHS -> 0
(python: 0.0056 at j = 10 for κ = 51/121, C = 0). So `dyadicNomeSchedule`
satisfies no `NomeScheduleAFCalibrated`; it is an interface witness only (its
`(1-w) side` is bounded, whereas AF calibration forces `(1-w) side ≍ A 2^j / j`).
The negative statement is not formalized.

## 6. Honest strength

* PROVED (unconditional): lag-shift pins; exact shifted telescope; shifted
  telescope bound; the shifted-H1 => A03 package compiler; shifted H2 => shifted
  H1; the shifted gap screen; the dyadic margin identity.
* OPEN: `PathShiftedEpsBound` (the single quantitative analytic input),
  `PathShiftedNondegenerate` (qualitative, fixed-scale), the schedule Props.
  Nothing consumes `NomeScheduleAFCalibrated`/`NomeSchedulePhysicalBox`; they
  record the requirement under which the shifted H1 is heuristically plausible
  (free-field eps*side ~ max(O(1), 2 m L_j), bounded iff `L_j` bounded).
* Unshifted box-kernel H1 and H2: heuristically FALSE (free-field spectral input
  and numerics, eps ~ 0.95); NOT proved false. Shifted H1: heuristically
  plausible under an AF-calibrated schedule; NOT proved.
* Screen persists: with any certified Rayleigh rate `r_j`, shifted H1 forces
  `side_j (1 - r_j) <= c0`, i.e. lattice gap `<= c0/side_j`; this is consistent
  with a fixed PHYSICAL gap when `L_j` is bounded, and incompatible with any
  fixed lattice rate `r < 1`.
* No new frontier closure, no chart change.

## 7. Verification

* Runs (all via `~/ymlean_prover_scratch/run_monitored_check.sh`,
  `safe_lean_build.py --jobs 1 --check-worker-limit-gib 8`, guard + snapshot +
  10 s sampler, abort at pressure >= 2 or avail < 8192 MiB):
  * p9a 20:44 PT: 3 errors (whnf timeout, rewrite miss) — fixed.
    peak load1 11.10, pressure 1, min avail 17809 MiB.
  * p9b 20:46 PT: 1 error (two-sided `RCscale_RCscale` rewrite) — fixed.
    peak load1 14.28, pressure 1, min avail 16747 MiB.
  * p9c 20:47 PT: clean. peak load1 13.50, pressure 1, min avail 16842 MiB.
  * p9final 20:47 PT with `--check-output .../BF4WilsonAllNomeShiftedH1Anchor.olean`:
    exit 0, 0 errors, 0 sorryAx. peak load1 12.16, pressure 1, min avail 16144 MiB.
* `#print axioms`: 26 gates; 23 print `[propext, Quot.sound]`; `lg2`,
  `NomeScheduleAFCalibrated`, `NomeSchedulePhysicalBox` print "does not depend
  on any axioms"; no `sorryAx`. Log:
  `~/ymlean_prover_scratch/logs/check-p9final-20261005-204731.out`.
* `python3 scripts/lean_forbidden_token_scan.py` (45 s, after root registration):
  `executable_forbidden_hits 0`.
* Docs: frontier paragraphs prepended (format-matched) in `docs/PROJECT-STATUS.md`,
  `lean/README.md`, `work_plan.md`; ledger entry; root import. No other sections edited.
