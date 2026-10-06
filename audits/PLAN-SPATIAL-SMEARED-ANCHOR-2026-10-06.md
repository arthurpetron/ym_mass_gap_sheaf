# PLAN: replace the Lean anchor Y_j by a spatially smeared zero-momentum loop (2026-10-06)

Status: this is a PLANNING NOTE ONLY. It makes no Lean edits and no Lean runs.
Nothing here is proved. Implementation waits for darthur's approval of the
switch (see section 7).

> **Update 2026-10-06 05:30 PT.** The side-10 point above is stream A only. Stream B gives
> W = 0.26(17) and eps*side = 1.898(87), versus 2.28(13) for A (about 2.4 sigma apart), and the two
> streams' operator means differ by about 4 sigma. So the side-10 errors are underestimated, and the
> large-lag W is sensitive to slow modes and vacuum subtraction. "No drift" at side 10 is not yet
> established. See `computations/ym_smoothed_mc/runs/WINDOW_SURVIVAL_s10_streamB.md`.

Motivation: the new Monte Carlo (`computations/ym_smoothed_mc/runs/WINDOW_SURVIVAL_partial.md`,
commit 805d4f84) measures `W = R(side+1)/R(side/2)` for a spatially smoothed,
zero-momentum `side×side` loop. At ρ = 1 it gives 0.203(27), 0.128(21), 0.223(40),
0.242(37), 0.355(60) and 0.23(12) at sides 2, 3, 4, 6, 8, 10, with no drift. That
is θ ≈ 0.2 for THAT state. By c944edfa, `PathShiftedWindowSurvival` with θ gives
shifted H1 with `c0 = 2(1-θ)/θ` (about 8 at θ = 0.2), and from there the
normalized-anchor package. The current Lean anchor `Y_j`, a box-time-smoothed
plaquette family, has never been measured. The question is what it would take
to make the Lean anchor the measured kind of state.

## 0. Repo facts this plan rests on (file:line, current HEAD)

* **Dense core.** `IntrinsicExpression width` (`BF4ExactSlabFixedSpatialWilsonIntrinsicForm.lean:45`)
  wraps a `WindowExpression` (`BF4ExactSlabFixedSpatialWilsonWindow.lean:50`). That is a
  POLYNOMIAL algebra with constructors `one`, `loop offset (value : SourceLoop width) spin`,
  `add`, `mul` and `smul (q : Q')`.
* **Loops are general.** `SourceLoop width` (`BF4ExactSlabFixedSpatialWilsonProbe.lean:44`)
  is ANY closed oriented link word with fields `start`, `edges`, `compatible`,
  `closed` and `physical : e.link ∈ baseLinks width`. So the carrier already
  represents loops larger than a plaquette. It also represents products of loop
  traces (`mul`), and products of links inside one trace (the word).
  `completed_loop_time_pairing` (`BF4WilsonAllNomeCompletedInner.lean:98`) holds for
  every `SourceLoop`.
* **How the current anchor is built.** `familyExpression width qs c hqs`
  (`BF4WilsonPlaquetteFamilySourcePin.lean:51`) is `Σ_p c_p · loop 0 (plaquetteLoop p) 1`,
  and `familyState` (`:69`) wraps it as an `IntrinsicExpression` with radius 0.
  The vector is
  `familyExcitation = centeredExcitation (familyState …)`
  (`BF4WilsonAllNomePlaquetteFamilyVariance.lean:147`).
* **Centering and vacuum complement are generic.** `centeredStream`, `centeredVector`,
  `centeredVector_orthogonal`, `centeredExcitation` and `centeredVector_time_pairing`
  (`BF4WilsonAllNomeCenteredVector.lean:118,129,147,152,159`) take ANY
  `x : IntrinsicExpression width`. `centeredTimeMoment n x y` with its Cauchy data
  (`BF4WilsonAllNomeCenteredMoments.lean:43`) is also generic.
  `VacuumComplement := {x // B U x = 0}` (`BF4WilsonAllNomeCompletedTime.lean:171`).
* **Anchor data are generic except the floor.** `NormalizedAnchorData`
  (`BF4WilsonAllNomeGenericNormalizedAnchor.lean:210`) needs a base state, a block,
  a `CReal` norm with `QCauchy` data pinned to `B(x, T^(2s) x)`, a positive rational
  floor, and a `TimeSector.State` witness for `T^s x`. For `Y_M` the data come
  from `repOrbit`, `familyStream`, `smoothedSector`, `smoothedNorm` and
  `smoothedAnchorData` (`:666,683,692,706,729`). Every one of these touches the
  family only through `familyState` / `centeredStream (familyState …)`; the rest is
  generic.
* **Floors are plaquette-specific.**
  * `varianceFloor` (`BF4ExactSlabPlaquetteAngularFamily.lean:117`) and
    `familyExcitation_norm_floor` (`…PlaquetteFamilyVariance.lean:151`, which
    needs `qs.Nodup`).
  * `family_bond_floor`, Bond ≥ ρ·Var with ρ depending on the nome and the
    family size (`BF4WilsonAllNomePlaquetteFamilyBondFloor.lean:188,217`).
  * The kinetic upper bound (`BF4WilsonAllNomePlaquetteFamilyKineticUpper.lean`).

  All of these run through plaquette angular coordinates or face lists.
* **No in-slice smoothing operator exists.**
  * `coeffW w s = dim(s)·w^{C4(s)}` (`BondMovingStep.lean:259`) and the
    `RGTransport` weights (`RGTransport.lean:45`) are single-link class-function
    and RG coefficient maps. They are not operators on the observable algebra of
    one time slice.
  * I found no APE, staple, gauge-averaging or conditional-expectation map acting
    on `IntrinsicExpression`.
  * A possibly useful tool for Haar integrals of loop words is
    `SU2QuaternionPolynomialHaarCarrier` (imported by the boundary carrier); to be checked.
* **Base links.** `baseLinks width` = links with `BoundaryLink width 0`
  (`BF4ExactSlabFixedSpatialBoundaryCarrier.lean:79-88`). Plaquette loops of
  `spatialFaces width` already live there. TO VERIFY: which spatial directions and
  coordinate ranges `SliceLink` admits, since staples must stay inside it.

## 1. A constructive spatial smearing on the completed carrier

### 1a. What a smeared vector ψ needs so that every generic (B,T) theorem applies

1. ψ is an `IntrinsicExpression width` (radius 0, all generators at offset 0, so
   it sits in one time slice). Then `R(n) = ⟨ψ, T^n ψ⟩` holds automatically, as an
   embedding of genuinely advanced expressions (`completed_loop_time_pairing`,
   `centeredVector_time_pairing`).
2. The anchor is `centeredExcitation ψ`. Membership in `VacuumComplement` and
   centering are then free; the representative is `centeredStream ψ`, which comes
   with Cauchy data.
3. The anchor-data inputs are free by copy:
   * the norm `CReal` comes from `centeredTimeMoment (2s) ψ ψ` with its Cauchy data;
   * the sector witness is `fromTime` of `timeNonexpansive (s-1)` applied to the
     representative.
4. Only a TRUE positive floor is not free, and that is section 2C.

### 1b. Smearing options

* **(A) RECOMMENDED: linear (unprojected) staple smearing.** Each step maps a link
  `U_ℓ` to `V_ℓ = (1-α) U_ℓ + (α/4) Σ_{4 spatial staples} U_staple` (a fixed
  rational α).
  * The smeared loop trace `(1/2) Tr Π V_ℓ` expands EXACTLY into a finite rational
    combination `Σ_w c_w · (1/2) Tr U_w` over closed spatial words `w`.
  * Each `w` is a `SourceLoop`, so `ψ = Σ_w c_w · loop 0 w 1` is literally of the
    same shape as `familyExpression`, with plaquettes replaced by words. It is
    gauge invariant (closed words), lies in the dense core, and needs no new
    semantics.
  * Zero momentum means summing over spatial translates (and over the 3 spatial
    planes, as the Monte Carlo does).
  * For SU(2) the smeared `V` is a quaternion with |V| ≤ (1-α) + α = 1, so the
    smeared trace is bounded. Unprojected smearing is natural in the quaternion
    picture.
  * In the free field, n steps diffuse the path with radius² ∝ α·n. To match
    Monte Carlo ρ ≈ 1 (radius ≈ ρ·side) take `n_j ≈ (ρ side_j)²/(c·α)` steps.
* **(B) A coefficient-smoothed plaquette family** (Σ_f c_f P_f with c a heat-kernel
  convolution). This stays inside the existing face framework, so the existing
  floors apply.
  * At ZERO momentum it does nothing: the zero-momentum family is already
    translation-uniform, so smoothing its coefficients leaves it unchanged. It
    stays the UV-dominated plaquette state.
  * The gain from smearing comes from replacing links by paths, which leaves the
    face framework. Rejected.
* **(C) APE or gradient flow with projection back to SU(2)** (what the Monte Carlo
  uses: `src/main.rs`, Euler/stout steps `U ← exp(ε P_su2[A U†]) U`).
  * The smeared link is `V/|V|` or an ODE solution. That is non-polynomial in the
    links and not in `WindowExpression`.
  * Representing it would need an L²-Cauchy sequence of polynomial approximants
    with an explicit modulus in the carrier seminorm, plus control where |V| → 0
    (a set of positive measure at finite β).
  * Constructively heavy and possibly infeasible near term. Not recommended.
* **(D) A transfer- or heat-kernel-type spatial operator on the algebra.** None
  exists in the repo. (A) IS the path-space random-walk version of such an
  operator, restricted to what the polynomial algebra can express.

**Caveat for (A):** the Monte Carlo numbers are for (C), not (A). Before the Lean
work, re-measure W with (A). This is a small Rust change: skip `renorm`/`exp` and
multiply unnormalized quaternions. W should then be compared at matched smoothing
radius.

## 2. Which consumers carry over

### 2A. Generic in (B, T, x): carry over UNCHANGED (any `x : V` or any NormalizedAnchorData)

* **Moments:** `mixedMoment` convexity, split and nonnegativity
  (`BF4WilsonAllNomeTimeDefectMoments`).
* **Window survival compiler:** `window_energy_antitone`, `window_telescope`,
  `window_energy_bound`, `window_epsBound`, `oneStepEpsBound_one`
  (`BF4WilsonAllNomeShiftedWindowSurvival`).
* **Lag-shift pins:** `shift_norm_pin`, `shift_response_pin` and `OneStepEpsBound`
  (`BF4WilsonAllNomeShiftedH1Anchor` §1).
* **Log-convexity, Jensen and block compilers:** completed log-convexity and
  `macro_ratio_of_survival_floor`, odd/even Jensen, the block compilers, and
  `block_survival_of_oneStep_energy`.
* **Rayleigh screen:** `WilsonVacuumRayleighRate` and
  `oneStep_energy_ge_of_rayleighRate`.
* **NormalizedAnchorData and the full consumer:** normalizer, `normalized_norm`,
  `block_floor`, `real_floor`, `real_increment`, `real_forward_increment`, the mesh
  increments, and the bond excitation.
* **Vacuum complement under time:** `completedTime_preserves_vacuumComplement`.

### 2B. Tied to the family / smoothed-state / trajectory structure: re-instantiate (mostly mechanical copy)

* **Smoothed-state data:** `repOrbit` is already generic; `familyStream`,
  `smoothedSector`, `smoothedNorm`, `smoothedNormCauchy`, `smoothedNorm_pin` and
  `smoothedAnchorData` need `familyState …` replaced by an arbitrary
  `e : IntrinsicExpression`. Generalize once as "expression-smoothed" data with
  M ≥ 0; the plaquette version becomes a special case.
* **Trajectory:** `DyadicSmoothedTrajectory`
  (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:329`) has plaquette fields (`faces`,
  `coeff`, `faces_spatial`, `faces_nodup`, `coeff_mass_pos`, `radiusFactor`). It
  needs a sibling `ExprAnchorTrajectory`: a schedule, `width j`, an expression
  `e j : IntrinsicExpression (width j)` and M_j. Here M_j = 0 (see section 4).
* **Shifted-H1 path theorems:**
  * `PathShiftedEpsBound` and `pathShiftedEpsBound_iff_response`;
  * `shiftedPathAnchor`, `path_shifted_macroRatio` and `path_shifted_anchor_floor`;
  * `ShiftedAnchorPackage` and `path_normalized_anchor_shifted`.

  The proofs use `tr.response j n = B(state, T^n state)` only definitionally, so
  they are copies with field renames.
* **Window-survival path theorems:** `PathShiftedNondegenerate`,
  `PathShiftedWindowSurvival`, `pathShiftedEpsBound_of_windowSurvival`,
  `path_normalized_anchor_of_windowSurvival` and `PathLagSurvival` (copies).
* **Not ported** (family- or time-smoothing-specific and not needed on the window
  route): the Fejér telescopes (`shifted_energy_le_familyResponse`,
  `smoothedEnergy_le_familyNorm`), H2 and `PathShiftedFamilySurvival`, and
  `smoothedNormFloor`.

### 2C. Needs NEW math

* **The nondegeneracy floor for ψ_j:** `PathShiftedNondegenerate`, i.e.
  `fl_j ≤ R_ψ(side_j)` with any positive j-dependent `fl_j`. It is the only input
  to the anchor norm floor; the floor `κ fl_j` then comes from the existing chain.
  * Natural route: a variance floor `Var(ψ_j) ≥ q_j > 0`, plus a one-step bond
    fraction `R(1) ≥ ρ_j R(0)` (the analogue of `family_bond_floor`), plus
    log-convexity, which gives `R(n) ≥ ρ_j^n q_j`.
  * Both are qualitative (the constants may be terrible), but none of the existing
    machinery applies to non-plaquette words.
  * Honest comparison: `PathShiftedNondegenerate` is OPEN for the current Y_j too.
    The switch loses no proved fact; it only loses the plaquette tools that might
    have discharged it.
* **`PathShiftedWindowSurvival` itself** stays OPEN. It is now supported by Monte
  Carlo (θ ≈ 0.2) for a neighbouring state.

## 3. Mapping the measured W to the Prop (exact)

* **The Lean side.** `PathShiftedWindowSurvival tr θ :≡ ∀ j ≥ 1,
  θ·R_j(side_j/2) ≤ R_j(side_j+1)`, where `R_j(n) = B(base_j, T^n base_j)` is the
  response of the UNSHIFTED base state. The shift is internal: shifted H1 is about
  `T^{side/2} base`, and the normalized anchor is `α·T^{side} base`. `side/2` is
  Nat floor division.
* **The Monte Carlo side.** `ana/window_analyze.py:74` computes `W = c[s+1]/c[s//2]` from
  the connected (centered) correlator of the unshifted, non-time-smoothed operator
  O. That is the same indices and the same floor.
* **Conclusion.** With `base_j := centeredExcitation ψ_j` and M_j = 0, the reduced
  Prop is literally `W_j ≥ θ` for the Lean state.
* **Remaining differences:**
  * smearing type: (A) in Lean vs flow (C) in the Monte Carlo;
  * action: the Monte Carlo uses the Wilson action, while the carrier uses nome
    character weights; the matching is a convention;
  * volume: periodic L_s³×L_t in the Monte Carlo vs the fixed-width padded slab
    in Lean;
  * plane averaging (easy to match).

## 4. Keep time smoothing and the shift?

* **Time smoothing: DROP it (M_j = 0).**
  * The Monte Carlo state has none, and W is measured without it.
  * It only Fejér-averages R, and its unconditional norm floor deteriorates like
    (M+1)^-2.
  * The window route does not need the time telescope.
  * Keep M as a parameter of the generalized construction for free (M = 0 is
    allowed), so nothing is lost.
* **Shift: KEEP it.** It is already built into the chain: window survival gives
  shifted H1 at `T^{side/2} ψ`, and the package's normalized state is
  `α T^{side} ψ`. Nothing extra is measured or proved.

## 5. Size, dependencies, difficulty

| new file (proposed) | content | lines (rough) | difficulty |
|---|---|---|---|
| F1 `BF4WilsonAllNomeSpatialPathWords` | oriented spatial words in slice 0; staple replacement; concatenation preserves `Compatible`/`closed`; `physical` under an interior-padding hypothesis (loop at distance ≥ n from the window edge); spatial translates | 500–800 | medium (combinatorics, omega-heavy; `Compatible`/`pathFinish` API to learn) |
| F2 `BF4WilsonAllNomeLinearSmearedLoop` | n-step linear smearing as a weighted word list (structural recursion, never enumerated); `ψ = Σ c_w loop 0 w 1`; zero-momentum and plane sum; `Within 0`; `centeredExcitation ψ`; response pin to `centeredTimeMoment` | 300–450 | low–medium |
| F3 `BF4WilsonAllNomeExprSmoothedAnchor` | generalize `smoothedCoherentVector`/`Sector`/`Norm`/`AnchorData` from `familyState` to any `IntrinsicExpression` (M ≥ 0) | 250–350 | low (copy-generalize) |
| F4 `BF4WilsonAllNomeExprAnchorTrajectory` | `ExprAnchorTrajectory`; ports of the 5d0196f7 §3–4 and c944edfa §2 path theorems; `path_normalized_anchor_of_windowSurvival` for ψ | 400–550 | low–medium |
| F5 `BF4WilsonAllNomeSmearedLoopNondegenerate` (optional) | variance floor and bond fraction for ψ_j; lag floor via log-convexity → `PathShiftedNondegenerate` | 800–2500+ | HIGH; feasibility uncertain |

* **Dependencies:**
  * F1: `SourceLoop`, `Compatible`, `pathFinish`, `baseLinks`, Z4 geometry.
  * F2: F1, `WindowExpression`/`IntrinsicExpression`, CenteredVector, CenteredMoments.
  * F3: CenteredVector, BilinearTime (`orbitSum`), GenericNormalizedAnchor
    (`kernelCSum`, `repOrbit`), TimeSector.
  * F4: F3, ShiftedH1Anchor (pins, `OneStepEpsBound`), ShiftedWindowSurvival
    (generic compiler), `NormalizedAnchorData`.
  * F5: F2 plus Haar/character tools (`SU2QuaternionPolynomialHaarCarrier`?) and
    the band/bond machinery.
* **Effort:** F1–F4 total about 1.5–2.2k lines, roughly 10–15 monitored single-file
  checks. The result: window survival (OPEN) plus nondegeneracy (OPEN) give the
  A03 package for the smeared-loop anchor, with no axioms.
* **Padding:** the current `trajWidth j = side_j² + 1` may be too small for
  `n_j ≈ (ρ side_j)²/(cα)` staple steps plus translates. F4 should carry its own
  width schedule; the old trajectory is not modified.
* **Engineering risk:** words are exponentially many (about 5^{4·side·n}). All
  proofs must be structural; no `decide`/`rfl` evaluation of the word list.

## 6. Riskiest lemma

**`smearedLoop_bond_floor`** (F5): at fixed nome w_j < 1 and width, for
`ψ_j = Σ_w c_w Tr U_w`,
`ρ_j · q_j ≤ B(ψ_j, T ψ_j)` with `q_j ≤ Var(ψ_j)` and `q_j, ρ_j > 0` rational.

Why it is risky:
* Every existing floor (`varianceFloor`, the angular coercivity,
  `family_bond_floor`) is proved through plaquette angular coordinates with
  distinct (`Nodup`) faces.
* Linear smearing produces words that share links, backtrack, or are cyclically
  equivalent. Distinct words can be the SAME function, so coefficients combine
  and can partially cancel.
* A positive variance needs a Haar/character computation for arbitrary words,
  which the repo does not have, plus a strict-nome transfer of the plaquette
  bond-band identity Var = Energy + Bond to general loops.

Mitigations:
* (i) Only qualitative per-scale constants are needed.
* (ii) Leave `PathShiftedNondegenerate` OPEN, the same status it has for Y_j
  today, and do F1–F4 first.
* (iii) Try to isolate the bare `side×side` loop term, with weight
  `(1-α)^{4·side·n}`, and lower-bound its variance via a Haar computation.

The second risk is F1's `physical`/padding lemma for concatenated staple words.
That is engineering, not math.

## 7. What darthur needs to approve

1. **The switch:** add a NEW anchor family `ψ_j = centeredExcitation(linearly
   smeared zero-momentum side_j×side_j loop)` with M_j = 0, alongside the existing
   Y_j chain (no deletions or edits of existing files).
2. **The smearing choice:** linear, unprojected staple smearing (A), instead of
   the Monte Carlo's projected flow (C). This means a cheap new Monte Carlo run
   with (A) to re-measure W before or alongside F1–F4.
3. **A new trajectory and width schedule** (`ExprAnchorTrajectory`, padded width),
   and the smearing parameter schedule (α, n_j ∝ (ρ side_j)²).
4. **Scope:** F1–F4 now, with `PathShiftedNondegenerate` (for ψ) and
   `PathShiftedWindowSurvival` remaining OPEN; F5 (the riskiest lemma) only as a
   separate decision.
