# RG-step composition reduction for the Wilson gap frontier (2026-10-06 PT)

Status: **REDUCTION ONLY.** No approximate intertwiner `Φ_j` is constructed.
Two-step intertwining (`T_f²` vs `T_c`) + proved transfer `r_F⁴ ≤ κ(r_C²+ε)`;
κ≥1 on pinned vacuum diagonals; one-step shape no-go; SC cannot seed `trAF`.
Companion Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeRGStepComposition.lean`.

## Question

Can the gap frontier on `trAF` (`WilsonAFPaddedGapInput`: a rate family with
`WilsonVacuumSqContraction` at each `(w_j, width_j)` and a dyadic lower margin
`m·2^{-j} ≤ 1 − r_j`) be restated as:

1. the existing open step-ratio input, and
2. inhabitability of approximate RG intertwiners `Φ_j` with summable weighted
   errors `Σ 2^j ε_j`, seeded by a known contraction at some coarse scale `j0`?

## Width / scale schedule (honest)

* YM Bot's sketch used width `2^j`. The live AF-padded trajectory `trAF` uses
  `width_j = trajWidth j = 4^j + 1` and physical spacing `a_j = 2^{-j}`
  (`BF4DyadicWilsonSquare.spacing`). These are **not** the same.
* The reduction below is **abstract in the scale index `j`**: it applies to any
  family with consecutive scales `(j+1) → j`, nomes `w_j`, widths `width_j`, and
  transfers `T_j = completedTime` on
  `BF4WilsonAllNomeCompletedInner.Completion (w_j) (width_j)`.
* Mapping to `trAF`: take the actual `(w_j, width_j)` of `trAF`. The factor-two
  intertwining `T_{j+1}² ↔ T_j` matches the dyadic spacing ratio
  `a_{j+1} = a_j / 2` (two fine lattice time steps ≈ one coarse physical step).
  The width jump `4^j+1 → 4^{j+1}+1` is **not** a spatial 2-blocking; any real
  `Φ_j` must account for that. The rate algebra does not care.

## Per-scale hypothesis (what would have to be inhabited)

At each `j`, an **approximate RG intertwiner**

```
Φ_j : VacuumComplement (w_{j+1}) (width_{j+1}) → VacuumComplement (w_j) (width_j)
```

together with errors `ε_j ≥ 0` and coercivity constants `κ_j > 0`, such that:

1. **Coercive lower bound** (prevents `Φ = 0`): `B_{j+1}(x,x) ≤ κ_j · B_j(Φx, Φx)`.
   Together with the upper bound ⇒ `κ_j ≥ 1` on any fine vacuum vector whose
   diagonal is pinned to a positive rational `δ` (`kappa_ge_one`).
2. **Norm upper bound**: `B_j(Φx, Φx) ≤ B_{j+1}(x,x)`.
3. **Approx intertwining (two fine steps vs one coarse; B-form):**
   `B_{j+1}(T_{j+1}² x) ≤ κ_j·B_j(T_j Φx) + (κ_j·ε_j)·B_{j+1}(x)`
   (`intertwine_twoStep`; constructive packaging of `Φ∘T² ≈ T∘Φ` without
   subtype subtraction). Matches the dyadic spacing ratio `a_{j+1}=a_j/2`.
4. **Rate transfer (PROVED from 1–3):** coarse VacSq at `r_j` ⇒ fine **two-step**
   factor `α = κ_j(r_j²+ε_j)`. Dictionary: VacSq at `r_F` ⇒ two-step factor
   `r_F⁴` (`vacuumSq_implies_twoStepFactor`), so choosing `r_F⁴ = α` gives
   `r_F⁴ ≤ κ(r_C²+ε)`. Writing `u_j = r_j²` recovers the 8a341453 shape
   `u_{j+1} ≤ u_j + ε'_j` after absorbing `(κ−1)·r_C²` into the effective
   defect `ε' = (κ−1)·r_C² + κ·ε` (`effectiveRgDefect`).

**No-go on the old one-step shape.** If a fine vector attains Rayleigh
`B(Tx)/B(x) ≥ r_C` (pinned diagonal), any one-step defect of the form
`B(Tx) ≤ κ·B(T Φx) + (κ·ε)·B(x)` plus coarse VacSq + upper forces
`r_C ≤ κ(r_C²+ε)`. When `r_C/κ > r_C²`, this lower-bounds `ε`; persistent
attainders along AF prevent `Σ 2^j ε_j` from staying small
(`oneStep_defect_forces_rate_le_kappa_factor`, `OneStepAfSumObstruction`).
This motivates the two-step retype.

Exact intertwiners (`ε_j = 0` with literal `Φ T² = T Φ`) almost certainly do
**not** exist for the Wilson action: different widths, different nomes `w_j`, no
exact blocking identity for continuum YM, and the AF width schedule is not a
pure 2-blocking. Any honest `ε_j` must come from quantitative RG / polymer /
continuum-limit estimates (Balaban-style or modern constructive QFT). **That
input is not supplied here.** Inhabitability of `Φ_j` remains **OPEN**.

## Rate algebra (proved, pure Q')

From `0 ≤ rFine ≤ 1` and `rFine² ≤ rCoarse + ε ≤ 1`:

* `1 − rFine ≥ (1 − rFine²)/2 ≥ (1 − rCoarse − ε)/2`.

So each RG step at least halves the available lattice margin, minus an
`ε`-penalty. Unfolding from a seed `r_{j0}` with partial weighted sums
`S_n = Σ_{k<n} 2^k ε_{j0+k}` bounded by some `S < 1 − r_{j0}` yields

* `1 − r_{j0+n} ≥ 2^{-n} (1 − r_{j0} − S)` (up to the precise indexing in Lean),

hence a dyadic lower margin `m · 2^{-j} ≤ 1 − r_j` with
`m ∼ (1 − r_{j0} − S) · 2^{j0}`. This is exactly the shape of
`WilsonLowerMargin` on `dyadicPhysicalSpacing`.

## Envelope PROVED from the κ chain (2026-10-06 ~9:35 PM PT; REDUCTION)

The old `RgMarginEnvelope` *assumed* its `∀ n` dyadic conjunct. It is now
**derived** (`rgKappa_dyadic_envelope`, `rgMarginEnvelopeκ_dyadic`) from three
hypotheses packaged in `RgMarginEnvelopeκ r ε κ j0 S U`:

1. `RgRateChainκ r ε κ j0` (two-step κ rate relation at each `j ≥ j0`);
2. `RgErrorSummable (effectiveDefectSeq κ ε r) j0 S`: `Σ_{k<n} 2^k eff_{j0+k} ≤ S`
   for every finite `n` (constructive partial sums), `eff_j = (κ_j−1)r_j² + κ_jε_j`;
3. relative upper margin `m_{j0+n} ≤ U·2^{-n}` (the B04 upper half; absolute
   `m_j ≤ M·2^{-j}` gives `U = M·2^{-j0}`).

Step actually used (`margin_after_rg_step_κ`, rewritten with `m = 1 − r`):
`m_{j+1} ≥ m_j/2 − (m_j² + eff_j)/4` — matches YM Bot's form exactly.
Scaled `a_n = 2^n m_{j0+n}`: `a_{n+1} ≥ a_n − U²·2^{-(n+1)} − ½·2^n eff_{j0+n}`
(`rgKappa_scaled_step`; the `m²` term is bounded using the upper margin, so the
B04 upper half is genuinely used). Telescoped (`rgKappa_envelope_invariant`):

* **Sharp:** `2^n·m_{j0+n} ≥ m_{j0} − U² − S/2`, i.e.
  `2^n·m_{j0+n} ≥ m_{j0} − M²·4^{-j0} − S/2`.
* **c = 1 form** (`rgKappa_dyadic_envelope_abs`): `2^n·m_{j0+n} ≥ m_{j0} − (M² + S)`.
* Half-power form: `2^{-n}(m_{j0} − U² − S/2) ≤ m_{j0+n}`.

**Non-vacuity condition (CORRECTED 2026-10-06 ~9:45 PM PT, per YM Bot review).**
Useful only if `m_{j0} > U² + S/2`. `U = M·2^{-j0} < 1` (`j0 > log₂ M`) is
**necessary but not sufficient**. In absolute units put `μ := 2^{j0}·m_{j0}` (seed
mass in `a_j = 2^{-j}` units; `μ ≤ M`) and `Ŝ := Σ_{j≥j0} 2^j eff_j = 2^{j0}S`. The
seed condition is then exactly

  `μ > M²·2^{-j0} + Ŝ/2`,

with output floor `m = μ − M²2^{-j0} − Ŝ/2` in physical units. Real requirements:
(a) defect tail `Ŝ < 2μ`, and (b) `2^{j0} > M²/(μ − Ŝ/2)`. Lean:
`rg_absolute_seed_lowerMarginFrom` (below). With the old step-ratio ceiling
`M ≥ 2^{2C+3}` and `C = 3`, `M² ≥ 2^18`: the seed sits ≈ `18 + log₂(1/μ)` dyadic steps
below the anchor. With the linear ceiling `M = 16(C+1) = 64`, `M² = 2^12`: ≈
`12 + log₂(1/μ)` steps.

**Rewired.** `rg_envelope_zero_lower_margin` and `rg_envelope_zero_wilsonLowerMargin`
now take `RgRateChainκ F.rate ε κ 0`, summable effective defect `S`, and
`WilsonUpperMargin F M`, and give the lower margin with seed
`rgSeedMarginκ = m_0 − M² − S/2` (positivity hypothesis). The assumed-envelope
version survives as `rg_envelope_zero_lower_margin_assumed` (legacy).
`exprWilsonFamily_lowerMargin_of_kappaChain` discharges the spacing by `rfl`.

**Spacing verdict.** The envelope uses `spacing j = half^j`. `exprWilsonFamily`,
`exprMixRateFamily` and `trajectoryDynamicFamily` (hence the `trAF` family) use
`dyadicPhysicalSpacing`, with `spacing j = half^j` **by definition**
(`exprWilsonFamily_spacing_half_pow := rfl`) — consistent. `afNomeSchedule`
(`1 − w_j = A/(j + κ⌊log₂(j+1)⌋ + 4)`, `A = 1/(16 b₀ ln 2)`) is calibrated with one
`j`-step = one halving of the spacing, so its scale relation also matches the
factor-2 RG step. Remaining mismatch (documented, not fixed): the widths
`4^j + 1` grow ×4 per step (not a spatial 2-blocking), and there is no concrete
`a(w)` (`NomeSchedulePhysicalBox` open), so the dyadic identification of the nome
schedule with the RG step is a calibration choice, not a theorem.

## Absolute seed lemma (2026-10-06 ~9:45 PM PT; REDUCTION)

Convention = `WilsonLowerMargin` / `WilsonLowerMarginFrom` (reused, already in the
file): `m · spacing j ≤ 1 − r_j`, `spacing j = 2^{-j}` (physical units).
Definitions: `seedMass r j0 = 2^{j0}·m_{j0}` (μ), `defectTail j0 S = 2^{j0}·S` (Ŝ),
`absSeedFloor r j0 S M = μ + −(M·M·2^{-j0}) + −(½·Ŝ)`.

`rg_absolute_seed_lowerMarginFrom F ε κ j0 S M hsp H hS hM0 hup hpos :
WilsonLowerMarginFrom F j0 (absSeedFloor F.rate j0 S M)` from
`spacing j = half^j`, `RgRateChainκ F.rate ε κ j0`,
`RgErrorSummable (effectiveDefectSeq κ ε F.rate) j0 S`, `0 ≤ M`, the absolute
ceiling `∀ j ≥ j0, F.latticeMargin j ≤ M · spacing j`, and the single finite
inequality `hpos : 0 < absSeedFloor F.rate j0 S M`.

## Ceiling sharpening: LINEAR in C (2026-10-06 ~9:45 PM PT; REDUCTION, packaging)

Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeStepRatioLinearCeiling.lean`.

**Verdict: the exponential `2^{2C+3}` is an artifact, not intrinsic.** Where it
comes from: (1) `block_pow_floor` gives window survival with `θ_C = (1/2)^{2C+2}`;
(2) `window_gap_compat` gives `θ ≤ (r²)^q`, `side = 4q`; (3) `side_rate_le_c0`
converts with `c0 ≥ 2(1−θ)/θ`, i.e. `c0 = 2^{2C+3} ≈ 2/θ_C`.
* Step (1)'s exponential IS intrinsic to window survival: a geometric response
  `R(n) = ρ^n` with `s(1−ρ) = c` has `R(s+1)/R(s/2) = ρ^{s/2+1} ≈ e^{−c/2}`, so no
  polynomial `θ` can be certified for the window ratio (math remark; not a Lean
  theorem).
* Step (3) is crude: `(r²)^q ≥ θ` gives `2q(1−r) ≤ 2q(−ln r) ≤ ln(1/θ)`, so the
  ceiling only needs `log(1/θ)`. The rational bound `x^q ≤ 1/(1+q(1−x))` used there
  turns `1/θ` into the ceiling.

New log-free step (3), by blocks: `q = pK + t` (`K = 2C+2`, `t < K`);
`(1/2)^K ≤ (r²)^q ≤ ((r²)^p)^K`; upper Bernoulli `x^p(1 + p(1−x)) ≤ 1`
(`upper_bernoulli`) and a `K`-th-root step (`le_one_of_pow_le_one`,
`block_rate_le_one`) give `p(1−r²) ≤ 1`; then `q(1−r) ≤ Kp(1−r²) + t ≤ 2K`:

* `side_rate_le_linear θ r q L K : L = 2(2q) → 0 ≤ r → r ≤ 1 → half^{K+1} ≤ θ →
  θ ≤ (r·r)^q → ofNat L · (1 − r) ≤ ofNat (8(K+1))`.
* `expr_stepRatio_forces_rate_linear` (same hypotheses as
  `expr_stepRatio_forces_rate_anyC`): `side_j(1 − r_j) ≤ 8(2C+2) = 16(C+1)` for
  `j ≥ max(2, j0)` (was `2^{2C+3}`).
* `wilsonUpper_of_stepRatio_linear`: `WilsonUpperMargin (exprWilsonFamily …)
  (ofNat (8(2C+2) + 2^{j0+2}))` (was `2^{2C+3} + 2^{j0+2}`). Since `j0` only needs
  `2C ≤ side j0 = 2^{j0}`, the minimal `j0` has `2^{j0+2} < 16C`: linear too.
* `stepRatio_absolute_ceiling_from … J (2 ≤ J) (j0 ≤ J)`: `∀ j ≥ J,
  latticeMargin j ≤ 16(C+1) · spacing j` — relative `U = 16(C+1)·2^{-J}` from `J` on,
  no small-scale term.
* `exprWilson_lowerMarginFrom_linearCeiling`: step-ratio inputs + κ chain from `J` +
  summable eff `≤ S` + `hpos : 0 < absSeedFloor r J S (16(C+1))` ⇒
  `WilsonLowerMarginFrom (exprWilsonFamily …) J (absSeedFloor r J S (16(C+1)))`.

Constants: at `C = 3`, `M = 64`, `M² = 2^12` (was `2^18`): the seed scale moves up
≈ 6 dyadic steps. The sharp log form would give `side(1−r) ≲ 2 ln(1/θ_C) ≈ 2.77(C+1)`
(and ≈ `c` with the sharp `θ ≈ e^{−c/2}`); `16(C+1)` is within a constant of that.
No no-go is needed: the exponential is removed under the CURRENT hypotheses. The
open inputs are unchanged (step ratio, H-var/H-ray, orbit contraction, κ chain,
summable defect, one finite seed inequality); Φ inhabitability still OPEN.

## Halving-time margin (2026-10-06 ~9:50 PM PT; REDUCTION, finite-check type)

Lean: `lean/YMGap/Continuum/BF4WilsonHalvingTimeMargin.lean`. Turns the MARGIN half
of the AF input into one integer certificate per scale: `r_j^{M0·2^j} ≤ 1/2`
(`n_j = M0·2^j` steps at spacing `2^{-j}` = constant physical time `M0`).

* `one_sub_pow_ge d (0 ≤ d) (d ≤ 1) n : 1 − n·d ≤ (1−d)^n` (from `bernoulli_pow`).
* `halvingMargin n := ⟨1, 2n−1⟩` (= `1/(2n)` for `n ≥ 1`).
* `margin_of_pow_le_half r n (0 < n) (0 ≤ r) (r ≤ 1) (r^n ≤ 1/2) :
  halvingMargin n ≤ 1 − r` (Bernoulli ⇒ `1/2 ≤ n(1−r)`, then cancel `n > 0`; no case
  split, no Classical).
* `wilsonLowerMargin_of_halvingTime F M0 (0 < M0) (spacing j = half^j)
  (∀ j, F.rate j^(M0·2^j) ≤ 1/2) : WilsonLowerMargin F (halvingMargin M0)`.
* `wilsonLowerMarginFrom_of_halvingTime F j0 M0 … (∀ j ≥ j0, …) :
  WilsonLowerMarginFrom F j0 (halvingMargin M0)`.
* `wilsonAFPaddedGapInput_of_halvingTime r hr0 hr1 Hc M0 (0 < M0)
  (∀ j, r j^(M0·2^j) ≤ 1/2) : WilsonAFPaddedGapInput`.

**Wiring verdict: direct fit** for the margin conjunct (`m = 1/(2M0)`, spacing by
`rfl`). Still OPEN: the rate family itself with `r_j < 1` and the all-vector
`WilsonVacuumSqContraction` on `trAF` (`Hc`), and the certificates. The
certificates must hold at EVERY `j` (the `From`-`j0` variant gives only
`WilsonLowerMarginFrom`, which `WilsonAFPaddedGapInput` does not accept directly).

## From-j0 closure of the halving-time margin (2026-10-06 ~10:00 PM PT; packaging)

Same Lean file. Closes the From-`j0` mismatch flagged above.

* `prefixRateMargin r m : Nat → Q'`, `0 ↦ m`, `k+1 ↦ min (prefixRateMargin r m k)
  ((1 − r k)·2^k)`: structural fold, decidable `Q'.min'` (no existential).
* `qmin_le_left`, `qmin_le_right`, `qmin_pos` (strict positivity survives `min`: the
  result IS one of the two inputs, so the cross-multiplied order needs no setoid care).
* `prefixRateMargin_pos (0 < m) (∀ j, r j < 1)`, `prefixRateMargin_le_base`,
  `prefixRateMargin_le_scale : j < k → prefixRateMargin r m k ≤ (1 − r j)·2^j`.
* `wilsonLowerMargin_of_from F j0 m (spacing j = half^j) (WilsonLowerMarginFrom F j0 m) :
  WilsonLowerMargin F (prefixRateMargin F.rate m j0)`. Uses the structure field
  `WilsonDynamicFamily.rate_lt_one` (no extra hypothesis). For `j < j0`:
  `m'·2^{-j} ≤ ((1−r_j)·2^j)·2^{-j} ≈ 1 − r_j`; for `j ≥ j0`: `m'·a_j ≤ m·a_j ≤ 1 − r_j`.
* `wilsonLowerMargin_of_halvingTimeFrom`, and
  `wilsonAFPaddedGapInput_of_halvingTimeFrom r hr0 hr1 Hc j0 M0 (0 < M0)
  (∀ j ≥ j0, r j^(M0·2^j) ≤ 1/2) : WilsonAFPaddedGapInput`
  (`m = prefixRateMargin r (1/(2M0)) j0`).

Verdict: the mismatch is closed; certificates are needed only for `j ≥ j0`. Rate family,
`r_j < 1` and the contraction `Hc` remain OPEN.

## Trace sandwich (2026-10-06 ~10:00 PM PT; proved finite lemmas)

Lean: `lean/YMGap/Continuum/SpectralTraceSandwich.lean`, on `SpectralGap.SpectralModel`
(`Continuum/SpectralGap.lean`; `λ_i ≥ 0` is the field `lam_nonneg`), `specMax`
(`Continuum/LocatedSpectralGap.lean`, running `Q'.max'` fold with a `0` floor) and
`finSum` (`Constructive/RationalTail.lean`).

* `excitedTrace S n := finSum (fun i => S.lam i ^ n) S.k`.
* `specMax_pow_le_excitedTrace S n (0 < n) : specMax S ^ n ≤ excitedTrace S n`.
* `excitedTrace_double_le S n : excitedTrace S (2*n) ≤ specMax S ^ n * excitedTrace S n`.
* `le_of_pow_le_pow a b (0 ≤ b) n (0 < n) (a^n ≤ b^n) : a ≤ b` (root-free).
* `specMax_le_of_trace_le S n (0 < n) U ρ (0 ≤ ρ) (s_n ≤ U) (U ≤ ρ^n) : specMax S ≤ ρ`.
* `specMax_pow_mul_ge S n A B (A ≤ s_{2n}) (s_n ≤ B) : A ≤ specMax S ^ n * B`.
* `specMax_pow_ge_of_ratio S n L (0 < s_n) (L·s_n ≤ s_{2n}) : L ≤ specMax S ^ n`.
* `specMax_ge_of_trace_bounds S n (0 < n) ρ A B (0 < B) (A ≤ s_{2n}) (s_n ≤ B)
  (ρ^n·B ≤ A) : ρ ≤ specMax S`.
* `specMax_mem_of_trace_bounds`: `ρlo ≤ specMax S ∧ specMax S ≤ ρhi`.

Hypotheses: `λ_i ≥ 0` (model field; even powers NOT needed because of it), `0 < n`
(the `k = 0, n = 0` edge `1 ≤ 0` is false), `0 < B` resp. `0 < s_n` for the lower bound.
All `Q'`, no `CReal`.

**Distance to `WilsonSpectralBridge.excitedCharSpectralGapData` (description only).**
`(excitedCharSpectralGapData op w hw0 hw1 N).model` IS a `SpectralModel`
(`excitedCharModel w hw0 N`: `k = N`, `lam i = qpow w (c4 (i+1))`, rational, nonnegative
by field, weights `dimQ (i+1)`), so every sandwich lemma applies to it with zero glue.
But: (1) its eigenvalues are closed-form, `specMax = w^3 = heatKernelSep` for `N ≥ 1`
(already the `LocatedSpectralGap.sep`), so the sandwich adds nothing there; (2) the
trace is UNWEIGHTED, while a physical `Tr T^n` carries multiplicities (`dimQ`, or its
square); a weighted variant needs `w_i ≥ 1`-type hypotheses (not proved); (3) the model is
tied to `op` only through the OPEN `CharacterDiagResolution` (Peter–Weyl/Schur in
`cinner`, `CReal.RC`-valued), so bounds on model traces say nothing about `op` without it;
(4) it is single-edge, fixed spacing, truncated to `N` modes, and not connected to the
`WilsonDynamicFamily.rate j` (an all-vector squared-norm contraction rate) at all. The
useful target is a model whose eigenvalues are NOT closed-form, with `s_n`, `s_{2n}`
bounded by a rigorous finite computation.

## Two-boundary envelope (2026-10-06 ~10:10 PM PT; REDUCTION)

Lean: `lean/YMGap/Continuum/RGTwoBoundaryEnvelope.lean`.

`TwoBoundaryRecursion K`: `u, lam, f : Nat → Q'`, `q, eta, a, CL, rho : Q'`, with
`u ≥ 0`, `0 ≤ q, η, a, CL`, `q < ρ < 1`, `aρ < 1`, and for `j < K`:
forward `u_j ≤ q u_{j+1} + η|λ_{j+1}| + f_{j+1}` (runs `K → 0`, datum `u_K`),
backward `|λ_{j+1}| ≤ a|λ_j| + a·CL·u_{j+1} + a f_{j+1}` (runs `0 → K`), pin `λ_0 = 0`
(`|·| = Q'.abs`).

Index check: the weight `ρ^{K−j}` is consistent with both directions. Forward: `q < ρ`.
Backward from the pin: the λ-recursion contributes `a Σ (aρ)^m`, finite iff `aρ < 1`.
No discrepancy with the requested shape.

Derived closure condition (weighted max, attained finite folds `X = max u_j ρ^j`,
`Y = max |λ_j| ρ^j`): with `α = ρ − q`, `β = 1 − aρ`,
`D := αβ − η·a·CL > 0`, i.e. `η·a·CL < (ρ − q)(1 − aρ)`.
Maximiser inequalities: `αX ≤ α u_K ρ^K + ηY + Fρ^K`; `βY ≤ a·CL·X + aFρ^K`
(the `j = 0` maximiser case uses the pin). Eliminating `Y`: `D X ≤ ρ^K (αβ u_K + (ηa+β)F)`.

Statements:
* `TerminalWeightedErrors f ρ K F := 0 ≤ F ∧ ∀ j ≤ K, f j ≤ F·ρ^{K−j}`.
* `twoBoundary_envelope R F hw (hD : 0 < closureDefect) C (hC : envelopeNum F ≤ D·β·C) :
  ∀ j ≤ K, u j + |lam j| ≤ C·ρ^{K−j}`, with
  `envelopeNum F = (β + a·CL)(αβ u_K + (ηa + β)F) + a·D·F`.
* `twoBoundary_envelope_explicit`: `C = envelopeConst = Num/(D·β)` (`Q'.divPos`).
* `closure_algebra` (the elimination), `forward_weighted`, `backward_weighted`,
  `wmax`, `le_wmax`, `wmax_attained`.

Comparison with `RgErrorSummable`:
* `rgErrorSummable_term_le`: `2^k ε_{j0+k} ≤ S` (sum condition forces each term).
* `terminalWeighted_of_rgErrorSummable (ρ ≥ 1/2)`: `RgErrorSummable (k ↦ f (K−k)) 0 S ⇒
  TerminalWeightedErrors f ρ K S`. After reflecting the index, the envelope's
  requirement is weaker: max not sum, and any base `ρ ∈ (q, min(1, 1/a))` instead of `1/2`.
* `exactForwardSystem` + `terminal_weighting_necessary`: on the exact forward system
  (`λ ≡ 0`) every envelope forces `f_{j+1} ≤ C ρ^{K−j}`; `far_end_error_forces_C`:
  `f_1 ≤ C ρ^K`.

**Verdict / discrepancy.** The claim "polynomially decaying `f` fit when `K` is the
endpoint" does NOT hold with a `K`-uniform constant. Geometric decay of `f` away from
the terminal scale is NECESSARY, so any `K`-independent far-end error `f_1` forces
`C ≥ f_1 ρ^{-K}`. The gain over `RgErrorSummable` is real but bounded: the anchor moves
to the terminal scale, the base improves from `1/2` to `ρ` (close to 1 when `q, aρ`
are small), and a max replaces the sum. Polynomial (AF) errors still need either
`K`-dependent constants or an extra mechanism.

## Trace bounds ⇒ halving time ⇒ margin (2026-10-06 ~10:40 PM PT; REDUCTION / finite check)

Lean: `lean/YMGap/Continuum/SpectralHalvingMargin.lean`.
* `specMax_pow_le_half_of_trace S n (0<n) U (s_n ≤ U) (U ≤ 1/2) : specMax S ^ n ≤ 1/2`.
* `specMax_le_one_of_trace` (same hypotheses): `specMax S ≤ 1`, so no extra hypothesis.
* `halvingMargin_le_of_trace` (same): `halvingMargin n ≤ 1 − specMax S`.
* `rate_pow_le_half_of_trace … r (0 ≤ r) (r ≤ specMax S) … : r ^ n ≤ 1/2`.
* `wilsonLowerMargin_of_traceCertificates F M0 (0<M0) hsp S U (hlink : ∀ j, F.rate j ≤
  specMax (S j)) (∀ j, excitedTrace (S j) (M0·2^j) ≤ U j) (∀ j, U j ≤ 1/2) :
  WilsonLowerMargin F (halvingMargin M0)`.
* `wilsonLowerMargin_of_traceCertificatesFrom` (all hypotheses only for `j ≥ j0`):
  `WilsonLowerMargin F (prefixRateMargin F.rate (halvingMargin M0) j0)`.

OPEN: `hlink`. Nothing ties `WilsonDynamicFamily.rate` to a finite spectral model. The
only model (`excitedCharModel`) is closed-form and tied to `op` only via the OPEN
`CharacterDiagResolution`. Volume uniformity is scoped separately:
`audits/SCOPE-C1-SQUARE-BOX-DOUBLING-2026-10-06.md`.

## Seeding by strong coupling (honest limits)

* `allNome_strongCoupling_vacuumSq` gives `WilsonVacuumSqContraction` at
  `timeRate = 1/4` for **every** literal width, under the three small-nome
  guards (`heatRatio ≤ 1/2`, `heatRemainderBound < 1`, entropy-rate).
* **Verdict on `trAF` / `afNomeSchedule`:** every scale fails the first guard.
  Proved: `afGap 0 < 1/2`, so `w_0 > 1/2`; by `nome_mono`, `w_j ≥ w_0` for all
  `j`; hence `heatRatio(w_j) ≥ heatRatio(1/2) = 4 > 1/2`
  (`not_heatRatio_le_half_afNome`). Strong coupling **cannot** seed `trAF`.
* The seed for the RG reduction on `trAF` is therefore an **open
  intermediate-coupling** contraction producer (neither SC nor a completed
  weak-coupling/AF producer).
* A constant rate still fails the B04 upper half
  (`constant_rate_not_all_scale_upper`). The composed family has rates that
  may rise toward 1 as `ε`-errors accumulate; the upper half remains the
  separate step-ratio input.

## What this does / does not do

| Does | Does not |
|---|---|
| Restate part of the gap frontier as inhabitability of `Φ_j` / `ε_j` | Construct any `Φ_j` |
| Prove the rate/margin algebra | Progress on Balaban-style estimates |
| Give a conditional path to `WilsonAFPaddedGapInput` | Discharge `WilsonAFPaddedGapInput` |
| Keep SC and AF labels honest | Feed SC rates into the AF capstone unconditionally |

## Restated frontier (REDUCTION)

On `trAF`, `wilsonGapBranch_afPadded_generic` still needs:

1. **Step ratio** (`ExprStepRatio`) — unchanged, open.
2. **`WilsonAFPaddedGapInput`**, which along this route splits as:
   * a seed contraction at some `j0` (SC cannot seed `trAF`; need an open
     intermediate-coupling producer), and
   * approx RG intertwiners with `Σ 2^j ε_j` small enough to leave a positive
     dyadic lower margin.

No new analytic estimate is claimed. Exact missing input: quantitative
construction of `Φ_j` (or direct verification of the rate-transfer Prop) with
summable `ε_j` for the Wilson action along the chosen schedule.

## Changelog

* 2026-10-06 ~8:40 PM PT — Retype to `intertwine_twoStep` (`T_f²` vs `T_c`);
  prove `approxRg_transfers_twoStep_factor` (`r_F⁴ ≤ κ(r_C²+ε)` dictionary);
  `kappa_ge_one`; `effectiveRgDefect = (κ−1)r_C² + κ·ε` in margin budget;
  one-step no-go `oneStep_defect_forces_rate_le_kappa_factor`. Still REDUCTION;
  `Φ` inhabitability OPEN. Axioms ⊆ {propext, Quot.sound}.
* 2026-10-06 ~9:35 PM PT — Envelope PROVED from `RgRateChainκ` + summable
  `eff` + B04 upper half (`rgKappa_dyadic_envelope`, sharp
  `2^n m_{j0+n} ≥ m_{j0} − U² − S/2`; c = 1 form with `M²+S`); zero-scale lower
  margin rewired through κ chain; spacing verdict recorded. REDUCTION; Φ OPEN.
* 2026-10-06 ~9:45 PM PT — Non-vacuity note corrected (μ > M²2^{-j0} + Ŝ/2;
  U < 1 necessary, not sufficient). Absolute seed lemma
  `rg_absolute_seed_lowerMarginFrom`. Linear ceiling `16(C+1)` replaces `2^{2C+3}`
  (`BF4WilsonAllNomeStepRatioLinearCeiling`). REDUCTION; Φ OPEN.
* 2026-10-06 ~9:50 PM PT — Halving-time margin (`BF4WilsonHalvingTimeMargin`):
  `r_j^{M0·2^j} ≤ 1/2` ⇒ `WilsonLowerMargin F (1/(2M0))`; direct fit into
  `WilsonAFPaddedGapInput` margin conjunct. REDUCTION.
* 2026-10-06 ~10:00 PM PT — From-`j0` closure (`prefixRateMargin`,
  `wilsonAFPaddedGapInput_of_halvingTimeFrom`; packaging) and trace sandwich
  (`SpectralTraceSandwich`; proved finite lemmas).
* 2026-10-06 ~10:10 PM PT — Two-boundary envelope (`RGTwoBoundaryEnvelope`): closure
  `η·a·CL < (ρ−q)(1−aρ)`, explicit `C`; terminal weighting necessary. REDUCTION.
* 2026-10-06 ~10:40 PM PT — `SpectralHalvingMargin` (trace bounds ⇒ margin; link OPEN) and
  the C1 scope note `SCOPE-C1-SQUARE-BOX-DOUBLING-2026-10-06.md`.
