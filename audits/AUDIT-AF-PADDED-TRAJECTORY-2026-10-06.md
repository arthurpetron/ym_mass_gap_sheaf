# Audit: AF-calibrated padded trajectory (2026-10-06)

Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean` (355 lines).
Axioms {propext, Quot.sound} (some definitions use none); no sorry.
The existing `paddedZeroMomentumTrajectory` (dyadic schedule) is kept unchanged.

> **CAVEAT: the constant `A = 3.883` is convention-dependent.**
>
> - `A = 1/(8 b0 ln 2) ≈ 3.883` assumes the CARRIER convention
>   `g² = t = −4 log w`. Here `w = e^{−t/4}` is the weight per Casimir unit
>   `C4 = 4 C2`, the heat kernel is `e^{−t C2}`, and so `1 − w ≈ g²/4`.
> - A **Wilson-action-matched** schedule would use **`A ≈ 1.942`**, half of
>   3.883. The check: the carrier heat kernel `e^{−t C2}` behaves at small `t` like
>   `exp(−θ²/t)` for `U = exp(iθ n·σ)`. That is the heat kernel on the unit 3-sphere
>   at time `t/4`, since unit-`S³` Laplacian eigenvalues `ℓ(ℓ+2) = 4 j(j+1) = 4 C2`.
>   The SU(2) Wilson weight is `exp((β/2) tr U) = exp(β cos θ) ≈ exp(−β θ²/2)`
>   with `β = 4/g²`. Matching the Gaussians gives `t = 2/β = g_W²/2`, i.e.
>   `g_W² = −8 log w` and `1 − w ≈ g_W²/8`. This halves `A` to `1/(16 b0 ln 2)`.
>   It agrees with the earlier note in `AUDIT-SHIFTED-H1-ANCHOR-2026-10-05.md`
>   (heat-kernel vs Wilson paragraph). This is leading-order weak-coupling matching
>   and is not in the repo. Higher-order matching and the ratio of lattice
>   Λ-parameters shift only the O(1) offset `C`. The two-loop `κ = 51/121` is unchanged.
> - **Which `A` is physically right (paper, leading order).** The universal
>   coefficients `b0`, `b1` belong to the STANDARD coupling normalization, with
>   continuum action `(1/4g²)∫F^aF^a` (SU(2) Wilson: `β = 4/g²`). The repo's
>   `g² = t` is only a label (`NonpertActivityHeatKernel.lean:66`). In standard
>   normalization the heat-kernel carrier has `g² ≈ 2t = −8 log w`. So the constant
>   that keeps `side_j·a(w_j)` bounded for THIS carrier is `A ≈ 1.942`, not 3.883.
> - Heuristic consequence: on `afNomeSchedule` (`A = 3.883`) the coupling is about
>   twice the calibrated one, so `a(w_j) ~ 2^{−j/2}` up to powers of `j`. The
>   physical box `side_j·a(w_j)` then GROWS like `~2^{j/2}` instead of staying
>   bounded.
> - In other words, `afNomeSchedule` has the two-loop SHAPE and satisfies the Lean
>   predicate `NomeScheduleAFCalibrated` with `A = 3.883`. It is physically
>   calibrated only if the repo's `t` were the standard `g²`, which leading-order
>   matching says it is not. A physically calibrated rational schedule would
>   replace `3883/1000` by about `1942/1000`. That is a one-constant change, plus
>   re-checking the numeric proofs in that file. It is not made here: no Lean edits
>   in this task.
> - **None of the Lean conclusions depend on `A`.** `NomeScheduleAFCalibrated`
>   appears only in its definition (ShiftedH1Anchor) and in this file. No downstream
>   theorem consumes it. `path_normalized_anchor_of_windowSurvival_padded` holds for
>   any schedule, so a Wilson-matched schedule (`A ≈ 1.942`) would get the same
>   A03 package conditional on window survival, with the same proof.
> - Whether window survival is TRUE does depend on `A`. Halving or doubling `A`
>   doubles or halves `g²` at each `j`, which changes the physical box
>   exponentially in `j` (previous bullet). So `A` matters for how plausible the
>   open input is, but for no Lean proof.
> - Below, "AF-calibrated" always means "two-loop shape, carrier convention
>   `A = 3.883`". It does NOT mean physically calibrated in the standard coupling
>   normalization (`A ≈ 1.942`).

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
- The Wilson-action matching caveat applies (see the caveat box at the top):
  Wilson matching gives `A ≈ 1.942`, not 3.883. `log2` is the integer surrogate `⌊log2(j+1)⌋`.
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
