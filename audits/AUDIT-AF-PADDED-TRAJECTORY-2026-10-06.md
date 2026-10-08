# Audit: AF-calibrated padded trajectory (2026-10-06)

Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean` (373 lines).
Axioms {propext, Quot.sound} (some definitions use none); no sorry.
The existing `paddedZeroMomentumTrajectory` (dyadic schedule) is kept unchanged.

> **COUPLING CONVENTION AND CALIBRATION (recalibrated 2026-10-06).**
>
> - **Conventions, stated once.**
>   - Carrier: weight per Casimir unit `w = e^{−t/4}`, heat kernel `e^{−t C2}`,
>     heat-kernel time **`t = −4 log w`**.
>   - The repo LABELS `t` as `g²` ("`g² = t`", `NonpertActivityHeatKernel.lean:66`).
>     That is a label, not the standard coupling.
>   - **Standard (Wilson-normalized) coupling: `g² = 2t = −8 log w`.** Continuum action
>     `(1/4g²)∫F^aF^a`; SU(2) Wilson `β = 4/g²`.
>   - Derivation: the carrier heat kernel is the unit-`S³` heat kernel at time `t/4`
>     (`ℓ(ℓ+2) = 4 j(j+1) = 4 C2`), so near the identity it is `~exp(−θ²/t)`. The
>     Wilson weight is `exp(β cos θ) ≈ exp(−βθ²/2)`. Matching gives `t = 2/β = g²/2`.
>     This is leading-order weak-coupling matching; it is not in the repo.
>   - **`b0 = 11/(24π²)` and `b1 = 17/(96π⁴)` refer to the STANDARD `g²`.**
> - **`afNomeSchedule` now uses the standard-normalization constant**
>   `A = 1942/1000`, against `1/(16 b0 ln 2) = 24π²/(176 ln 2) = 1.9416585…`
>   (error `3.4·10⁻⁴`, relative `1.8·10⁻⁴`). Also `κ = b1/(2b0²) = 51/121`, which
>   is convention-independent, and `C = 4`.
> - **History.** Through `c0ffb7f6` the file used `A = 3883/1000 = 1/(8 b0 ln 2)`.
>   That value treats the label `t` as the standard `g²`. With it, the physical box
>   `side_j·a(w_j)` would grow like `~2^{j/2}`.
> - **Remaining honest caveats.**
>   - Two-loop SHAPE only. Also, a rational `A` with relative error `δ` makes
>     `L_j` drift like `2^{δ j}`. Here `δ ≈ 1.8·10⁻⁴`, so `L_j` doubles only around
>     `j ≈ 5700`: slow, but not bounded.
>   - `⌊log2(j+1)⌋` is an integer surrogate.
>   - `C = 4` is a choice. It absorbs the lattice Λ-parameter ratio and higher
>     orders, and it sets the box size in units of `Λ⁻¹` (`LΛ ∝ 2^{−C}`).
>   - There is no concrete `a(w)`, so `NomeSchedulePhysicalBox` is not addressed.
>   - **The calibration is cosmetic for the Lean conclusions.**
>     `NomeScheduleAFCalibrated` is consumed by no downstream theorem, and
>     `path_normalized_anchor_of_windowSurvival_padded` holds for any schedule.
>     `A` matters only for how plausible window survival is.
> - **Docstring still to update.** The docstring of `NomeScheduleAFCalibrated`
>   (`BF4WilsonAllNomeShiftedH1Anchor.lean:652-657`) said "`g² = t = -4 log w`
>   … `A ≈ 3.883`". It now states `A = 1/(16 b0 ln 2) ≈ 1.942` with the
>   standard `g² = 2t = −8 log w`. This was done after approval, with a monitored
>   4-module rebuild; see "Convention pass" below.

## Concrete precision inputs produced (2026-10-08 UTC)

The fixed-rounding caveat above remains valid. Its next constructive remedy
now has actual rational-series inputs rather than an assumed enclosure:

- `lean/YMGap/Constructive/Pi.lean:1198`, `pi_approx_enclosure`, bounds every
  later actual Machin approximation between `piLower n` and `piUpper n`.
  The positive arctan tail enters the upper endpoint and the SUBTRACTED
  arctan tail enters the lower endpoint; n=0 is included.
  `:1268`, `pi_enclosure_width_le`, bounds the width by 20*half^n;
  `:1295`, `pi_enclosure_width_le_of_modulus`, uses the explicit data
  `piEnclosureModulus eps := ((1/20)*eps).den`.
- `lean/YMGap/Constructive/CRealLog.lean:917`, `log2Lower_le_approx`, and
  `:924`, `log2_approx_le_upper`, bound every later ACTUAL doubled-artanh
  approximation. The width data are `(9/4)*half^n`, with explicit
  `log2EnclosureModulus eps := ((4/9)*eps).den` and its theorem `:959`,
  `log2Tail_le_of_modulus`. `:949`, `twoThirds_le_log2Lower`, supplies the
  denominator floor for n>=1; the zero-index lower endpoint is zero and
  must NOT be inverted. Both leaves also prove limit-order corollaries
  for the SAME `Pi.pi` / `CRealLog.log2`.

Observed verification: Pi focused check 1 PASS; log2 focused check 2 PASS.
Independent review read BOTH complete frozen final sources (1348 Pi lines,
1049 log2 lines), revalidated their source/log hashes, and found no defect
in the new mathematics or scope. Root inspected every addition and actual
series/monotonicity/precision input. The separate measurement-map review
also PASSes its historical-scope correction; no measured premise is added.
The first log2 attempt had a local `Q'.mul_pos` argument-arity error, then
the corrected complete leaf passed. All 17 new printed gates are permitted
(three Pi data definitions axiom-free; the log2 modulus bound uses only
propext). One compiler at a time, 20-GiB ceiling, 12-GiB reserve, fresh
successful preflight before each launch; zero swap and 85--87% reported
free memory. No limits raised, new premise, sorry, custom axiom, classical
input, native decision, root build, full-tree audit or baseline refresh.

Frozen source/log evidence:

    Pi source SHA256 b053a366d83ff827c8fd183f59607246c329ea1aca02422fbfcb5c6addf6ab08
    /private/tmp/ym-oct8-pi-enclosure1.log
    log SHA256 e753374b33a0cc9e841d33854a37a05097ca6b5bdd3a219689908f2db6947a24
    log2 source SHA256 6dcfeb881654a61f2927f5f5dc4d9eda19af501967f71b4ceee1d0fc385f8d94
    /private/tmp/ym-oct8-log2-enclosure2.log
    log SHA256 355bd56f337094c6a04dbd68decc4b57aa0f17319fc1234ed70f598076069eee

NEXT, not yet a Lean theorem: for positive pi lower endpoint P, upper Q<=8,
and 2/3<=l<=u for log2, the rational coefficient interval
`[3*P^2/(22*u), 3*Q^2/(22*l)]` has width <=110*half^n.
The bounded PAPER quotient calculation was independently checked, but its
actual CReal reciprocal/limit pin, coefficient enclosure and decreasing
running-min producer still need implementation. Existing
`PositiveRationalCauchyReciprocal.reciprocalCauchy` / `mul_value` accept
the shifted actual log stream with its EXPLICIT QCauchy data and 2/3 floor;
no choice from `CReal.cauchy` is permitted. This is a scalar two-loop precision
construction, not a concrete physical a(w), justified RG family or gap.
The original rounded schedule, endpoints and canonical fields are unchanged.
Original signed-family payment, continuum/QFT/every-group/Clay remain OPEN;
the canonical chart's displayed claims are unchanged.

## 1. The dyadic schedule is not AF-calibrated (PROVED)

```lean
theorem dyadic_not_AFCalibrated (A kappa C : Q') :
    ¬ NomeScheduleAFCalibrated dyadicNomeSchedule A kappa C
```

This holds for every `A, κ, C`, including `A ≤ 0`, where the first conjunct fails anyway.
The proof is constructive and uses an explicit witness scale. Put `K = |κ.num|`,
`Cn = |C.num|`, `D = den A` and `j = 2·D·(2 + 2K + Cn)`.

- Rational Archimedean bounds give `κ ≤ K` and `C ≤ Cn`. With
  `⌊log2(j+1)⌋ ≤ j` (`Nat.log2_lt`) this gives
  `j + κ lg2 j + C ≤ N := j + K j + Cn`.
- `1 - w_j = 2^-(j+1)` exactly: `half^n` has numerator 1 and denominator `2^n`.
- `A ≥ 1/D` because `A.num ≥ 1`. So the upper calibration inequality forces
  `2^(j+1) ≤ N·D`.
- A Nat lemma gives `N·D ≤ P² < 2^(2P) < 2^(1+j)` with `P = D(2+2K+Cn)` (via `P < 2^P`).
  This contradicts the previous bullet.

This formalizes the earlier paper statement `(1 - w_j)·side_j = 1/2`
(`dyadicNomeSchedule_margin_side`). The dyadic margin `2^-(j+1)` is exponentially smaller
than the AF margin `≍ A/j`.

## 2. The AF-calibrated rational schedule

```lean
def afE (j : Nat) : Nat := 121 * j + 51 * Nat.log2 (j+1) + 484
def afA : Q' := Q'.mkPos 1942 1000 _        -- A = 1.942 ≈ 1/(16 b0 ln 2)
def afKappa : Q' := Q'.mkPos 51 121 _       -- κ = 51/121
def afC : Q' := 4
def afGap (j : Nat) : Q' := Q'.mkPos 234982 (1000 * afE j) _
  -- 1 - w_j = A / (j + κ⌊log2(j+1)⌋ + 4) = (1942·121)/(1000·121·D_j)
def afNomeSchedule : NomeSchedule where
  nome := fun j => 1 - afGap j
  limitModulus := fun eps => 4 * eps.den      -- explicit
  ...
theorem afDen_gap (j) : (Q'.ofNat j + afKappa * lg2 j + afC) * afGap j ≈ afA   -- exact
theorem afNomeSchedule_AFCalibrated :
    NomeScheduleAFCalibrated afNomeSchedule afA afKappa afC
```

The `NomeSchedule` fields are proved with exact Int cross-multiplication:

- `nome_pos`: `afGap j < 1`, since `1000·121·D_j ≥ 484000 > 234982`.
- `nome_lt_one`: `afGap j > 0`.
- `nome_mono`: `afGap` is antitone because `D_j` increases. This uses monotonicity of
  `Nat.log2` (`Nat.le_log2`, `Nat.log2_self_le`).
- `nome_limit`: for `j ≥ 4·den ε`, `afGap j ≤ ε`, because `121·1000·j ≥ 484000·den ε` and `num ε ≥ 1`.

Calibration holds with `C = 4`. The upper side `A ≤ (j + κ lg2 j + 4)(1 - w_j)`
is an equality up to `≈`. The lower side uses `-4 ≤ 4` and `1 - w_j ≥ 0`.

What "AF-calibrated" means here, honestly:

- Two-loop running predicts the SHAPE `1 - w_j = A/(j + κ log2 j + C)`, with
  `κ = b1/(2 b0²) = 51/121` and `A = 1/(16 b0 ln 2) ≈ 1.9417`, in the STANDARD
  coupling `g² = −8 log w` (so `1 - w = g²/8 + O(g⁴)`).
  - This requires `side_j = 2^j` lattice steps to have bounded physical length.
  - See the box at the top, and `AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md`, which
    states the carrier `t = −4 log w` convention.
- `log2` is the integer surrogate `⌊log2(j+1)⌋`. `A = 1942/1000` is a rational
  approximation.
- `C = 4` is a choice: `w_0 = 1 − A/4 = 0.5145 ∈ (0,1)`, and the exact identity
  `afDen_gap` holds because `afE` contains `121·C = 484`.
- `NomeSchedulePhysicalBox` is NOT addressed. The repo has no concrete
  lattice-spacing function `a(w)`. `PhysicalSpacingEnvelope.a` in the AF
  bridge files is an abstract interface field, and the two-loop `a(g)` involves
  `exp`/`log` of `1/g²`. I did not invent one.
- `NomeScheduleAFJustified` (∃ `AFRateModulus` matching the nome) was not
  attempted. It looks inhabitable for this schedule (`A/(j+4)` upper, `A/(2(j+4))`
  lower), but it is not needed.

## 3. The AF padded trajectory and its A03 package

```lean
def afPaddedZeroMomentumTrajectory : DyadicSmoothedTrajectory :=
  { paddedZeroMomentumTrajectory with schedule := afNomeSchedule }
theorem afPaddedZeroMomentum_AFCalibrated :
    NomeScheduleAFCalibrated afPaddedZeroMomentumTrajectory.schedule afA afKappa afC
theorem afPaddedZeroMomentum_padded : PathFacesPadded afPaddedZeroMomentumTrajectory
theorem afPaddedZeroMomentum_nondegenerate :
    PathShiftedNondegenerate afPaddedZeroMomentumTrajectory
      (paddedNondegFloor afPaddedZeroMomentumTrajectory)
theorem af_path_normalized_anchor_of_windowSurvival
    (c0 theta delta : Q') (a : Nat) (ha : 1 ≤ a)
    (h0 : 0 < theta) (h1 : theta ≤ 1)
    (hc0 : (1 + -theta) * Q'.ofNat 2 ≤ theta * c0) (hc1 : 1 ≤ c0)
    (hdelta0 : 0 ≤ delta) (hdelta : delta < 1)
    (hcd : c0 ≤ Q'.ofNat (side a) * delta)
    (Hw : PathShiftedWindowSurvival afPaddedZeroMomentumTrajectory theta) :
    ShiftedAnchorPackage afPaddedZeroMomentumTrajectory delta hdelta a
      (paddedNondegFloor afPaddedZeroMomentumTrajectory)
      (paddedNondegFloor_pos afPaddedZeroMomentumTrajectory)
theorem af_path_normalized_anchor_of_halfSurvival
    (Hw : PathShiftedWindowSurvival afPaddedZeroMomentumTrajectory afHalf) :
    ShiftedAnchorPackage afPaddedZeroMomentumTrajectory afHalf _ 2 (paddedNondegFloor _) _
    -- θ = 1/2, c0 = 2, a = 2, δ = 1/2, κ = (1/2)^4
```

The faces, coefficients and radius are the same as `paddedZeroMomentumTrajectory`:
all faces of `spatialFaces (side_j²)`, unit coefficients, `M_j = side_j`.
The only open input is `PathShiftedWindowSurvival afPaddedZeroMomentumTrajectory θ`.

## Does anything use the nome schedule?

The schedule enters the A03 conclusions only as the carrier nome `w_j`. The
completed carrier, `T` and `B` at scale `j` are those at `w_j`, so the package
is a statement about the AF-calibrated carriers. No theorem in the chain
consumes `NomeScheduleAFCalibrated`, `NomeSchedulePhysicalBox` or any
property of `w_j` beyond `0 < w_j < 1`. The convexity compiler, the shifted
telescope, the padded floor and the normalized-anchor package all hold for
ANY schedule. For the Lean conclusions the calibration is therefore cosmetic.
It matters only for whether `PathShiftedWindowSurvival` is plausible: that
Prop is false at any fixed coupling (see
`MATH-NOTE-WINDOW-SURVIVAL-ROUTES-2026-10-06.md`) and can hold only if the
lattice correlation length grows like `side_j`, which is what the AF
calibration is designed to arrange.

## Checks

The monitored olean build of `BF4WilsonAllNomeShiftedPaddedNondegenerate` was needed
for the import: exit 0, ~13.4 min (`lake` rebuilt stale dependencies; one worker,
8 GiB limit), peak load1 14.9, pressure level ≤ 1, ≥ 20.3 GiB available. The monitored
single-file check of the new file: exit 0, ~11 s, no warnings, ≥ 21.2 GiB available.
The arithmetic was developed against stub definitions in a throwaway box-local
Lean project, not on the Mac. Forbidden-token scan: 0 hits.

## Recalibration and convention pass (2026-10-06)

- **Recalibration (`eb7cab00`).** `afA` changed from 3883/1000 to 1942/1000. The numerals
  in the `afGap*` and `afDen_gap` proofs were updated; no names changed. The monitored
  single-file check passed: exit 0, about 10 s, no warnings, at least 20.4 GiB
  available, pressure level 1. Axioms: {propext, Quot.sound} or none.
- **Convention pass, Lean docstrings.** Edited, docstrings only:
  - the `NomeScheduleAFCalibrated` docstring (`BF4WilsonAllNomeShiftedH1Anchor`);
  - the `NonpertActivityHeatKernel` module header and the `charMoment_le_g2` line;
  - the `ExactSinglePolymerActivity` module header.
- **Rebuild-chain review (import graph).** Transitive reverse dependents per module:
  - `ShiftedH1Anchor`: 4 (`ShiftedWindowSurvival`, `ShiftedPaddedNondegenerate`, this
    AF file, root `YMGap`);
  - `NonpertActivityHeatKernel`: 1 (root);
  - `ExactSinglePolymerActivity`: 1 (root);
  - `FieldSpaceCluster`: 30;
  - `SinglePolymerGaussian`: 19;
  - `FieldSpaceRenormalonZ1`: 8994.

  The last three were NOT edited. Their docstrings are listed in
  `docs/CONVENTIONS-COUPLING.md`.
- **Pre-build check.** `lake build --no-build`, run through the launcher, confirmed that
  every other upstream olean was up to date and only the AF olean was stale.
- **Rebuild.** One monitored session under `nice -n 10`, `LEAN_NUM_THREADS=2`, one job
  per build and an 8 GiB worker cap, one Lean process at a time. The session had a
  process-group timeout and a 10 s sampler. Abort rules: pressure warning or critical,
  available RAM < 8 GiB, or load1 > 14 for 6 consecutive samples.
- **Rebuild order and wall times** (from olean timestamps):
  1. `ShiftedH1Anchor` about 14 s;
  2. `ShiftedWindowSurvival` about 7 s;
  3. `ShiftedPaddedNondegenerate` about 5 s;
  4. this AF file about 4 s (refreshing its stale olean);
  5. `NonpertActivityHeatKernel` about 1 s;
  6. `ExactSinglePolymerActivity` about 1 s.

  The root `YMGap` olean was not rebuilt.
- **Outcome.** All exits 0, no abort, no wait. Peak load1 11.48, which is darthur's own
  Mac apps; the box Monte Carlo runs do not run on the Mac. Peak pressure level 1, at
  least 19.3 GiB available, swap unchanged at 929 MB.
- **Follow-up checks.** Single-file checks of the three edited files printed axioms
  {propext, Quot.sound} or {propext} or none, with no warnings. The forbidden-token scan
  found 0 hits.
