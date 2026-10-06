# Audit: AF-calibrated padded trajectory (2026-10-06)

Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean` (355 lines).
Axioms {propext, Quot.sound} (some definitions use none); no sorry.
The existing `paddedZeroMomentumTrajectory` (dyadic schedule) is kept unchanged.

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
def afA : Q' := Q'.mkPos 3883 1000 _        -- A = 3.883
def afKappa : Q' := Q'.mkPos 51 121 _       -- κ = 51/121
def afC : Q' := 4
def afGap (j : Nat) : Q' := Q'.mkPos 469843 (1000 * afE j) _
  -- 1 - w_j = A / (j + κ⌊log2(j+1)⌋ + 4) = (3883·121)/(1000·121·D_j)
def afNomeSchedule : NomeSchedule where
  nome := fun j => 1 - afGap j
  limitModulus := fun eps => 4 * eps.den      -- explicit
  ...
theorem afDen_gap (j) : (Q'.ofNat j + afKappa * lg2 j + afC) * afGap j ≈ afA   -- exact
theorem afNomeSchedule_AFCalibrated :
    NomeScheduleAFCalibrated afNomeSchedule afA afKappa afC
```

The `NomeSchedule` fields are proved with exact Int cross-multiplication:

- `nome_pos`: `afGap j < 1`, since `1000·121·D_j ≥ 484000 > 469843`.
- `nome_lt_one`: `afGap j > 0`.
- `nome_mono`: `afGap` is antitone because `D_j` increases. This uses monotonicity of
  `Nat.log2` (`Nat.le_log2`, `Nat.log2_self_le`).
- `nome_limit`: for `j ≥ 4·den ε`, `afGap j ≤ ε`, because `121·1000·j ≥ 484000·den ε` and `num ε ≥ 1`.

Calibration holds with `C = 4`. The upper side `A ≤ (j + κ lg2 j + 4)(1 - w_j)`
is an equality up to `≈`. The lower side uses `-4 ≤ 4` and `1 - w_j ≥ 0`.

What "AF-calibrated" means here, honestly:

- The SHAPE `1 - w_j = A/(j + κ log2 j + C0)` with `κ = b1/(2 b0²) = 51/121`
  and `A = 1/(8 b0 ln 2) ≈ 3.883` is what two-loop running predicts. It assumes the
  repo's coupling convention `g² = t = -4 log w` (so `1 - w = g²/4 + O(g⁴)`)
  and requires `side_j = 2^j` lattice steps to have bounded physical length
  (see `AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md`).
- The Wilson-action matching caveat still applies. The heat-kernel nome is
  not the Wilson `β`, and matching changes `A` by an O(1) factor (≈1.94 vs
  3.88 in the earlier note). `log2` is the integer surrogate `⌊log2(j+1)⌋`.
  `A` is a rational approximation, and `C0 = 4` is just chosen so that `w_0 ∈ (0,1)`.
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
