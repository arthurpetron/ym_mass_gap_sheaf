# Plan: fixed-physical-volume carrier (scoping only, 2026-10-06)

PAPER ONLY. No Lean was edited or run for this note. Nothing here is proved.
It scopes Route 1 of `audits/MATH-NOTE-WINDOW-SURVIVAL-ROUTES-2026-10-06.md`: a carrier
whose spatial width grows like `side_j` (fixed physical box), not like `side_j²`
(growing physical box).

**Bottom line**
- The Lean port is cheap and mechanical, about 0.55–0.9k lines.
- It turns the open input `PathShiftedWindowSurvival` into a small-volume,
  ultraviolet-type statement. Balaban-type methods are aimed at that regime, but
  they do not prove it. A named bridge is missing (§3).
- It does NOT bring the infinite-volume gap any closer. The hard part moves to the
  thermodynamic (IR) limit, and the fixed-volume A03 package says nothing about the
  infinite-volume gap (§4).
- Recommendation (§6): not a better critical path. If done at all, do it after
  darthur's F1–F4 decision, folded into one width-generic trajectory.

## 1. Setup

### 1.1 Today's carrier
- `trajWidth j = side j * side j + 1`, hard-wired
  (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean:310`). Related lemmas are
  `trajWidth_gt_side` (:312) and `trajWidth_ratio : side j * side j < trajWidth j`
  (:318).
- `DyadicSmoothedTrajectory` (:329) fixes the carrier at scale `j` to be the completed
  Wilson/heat-kernel slab carrier at nome `w_j` with spatial width `trajWidth j`. Its
  field `faces_spatial` requires `faces j ⊆ spatialFaces (trajWidth j)`.
- Time is unbounded: `completedTime` at any lag, as in the OS/transfer-matrix picture.
- The padded zero-momentum family uses `faces j = spatialFaces (side j * side j)`
  (`paddedZeroMomentumTrajectory`, `BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:251`).

### 1.2 Physical units
The repo measures physical length in units of `L`, with
`spacing j = half^j = 1/side_j` and `side_j·spacing_j = 1`.
`dyadicPhysicalSpacing` (:583) is the spacing set by fiat. It is NOT derived from
`w_j`. So today:
- the time window (lags `side_j/2 … side_j+1`) is about `L/2 … L`, a fixed physical
  time;
- the spatial width is `side_j²·a_j = side_j·L`, which grows without bound.

### 1.3 Fixed-volume variant
- Width: `width_j = c·side_j + 1` with a fixed integer `c ≥ 1`.
- Padding base: `base_j = c·side_j < width_j`.
- Physical spatial box: about `cL` (fixed). Time stays unbounded, so the object is a
  transfer matrix on a fixed spatial box of size `cL`.
- Lattice spacing: `a_j = L/side_j → 0`.

### 1.4 How `a_j` relates to the nome (honest status)
- `a_j` is not a free parameter. Physically it must be `a(w_j)`, the spacing of the
  lattice theory at nome `w_j` in units of the dynamical scale `Λ⁻¹`. Fixing the box
  then means `side_j·a(w_j) ∈ [Llo, Lhi]`.
- That condition is `NomeSchedulePhysicalBox ns a Llo Lhi`
  (`BF4WilsonAllNomeShiftedH1Anchor.lean:667`). Its argument `a : Q' → Q'` is a
  PARAMETER. **The repo has no concrete `a(w)`.** `PhysicalSpacingEnvelope.a` in the
  BF4 AF/physical-separator files is an abstract field.
- On paper, two-loop running gives `1 − w_j ≈ A/(j + κ log₂ j + C)` with
  `κ = 51/121`. In the standard coupling normalization the heat-kernel carrier needs
  **`A ≈ 1.942`** (caveat box in `audits/AUDIT-AF-PADDED-TRAJECTORY-2026-10-06.md`).
  With the checked `afNomeSchedule` (`A = 3.883`) the box would grow like about
  `2^{j/2}`, so it is NOT a fixed-volume schedule.
- The offset `C` sets `L` in units of `Λ⁻¹`. A small physical box (`g²(L)` small)
  means `C` large.
- Any fixed-volume instance should use a recalibrated `A ≈ 1942/1000`. It stays
  calibrated only on paper: no Lean statement can say "physical" without a concrete
  `a(w)`.

### 1.5 Boundary conditions
`spatialFaces width` lists the time-slice plaquettes with spatial coordinates
`< width` (`spatialIds_faces_mem_iff`, `BF4ExactSlabFixedSpatialFacePlacement.lean:38`).
As far as the face enumeration shows, there is no wraparound: the box is open/free
in space. Balaban's finite-volume work uses a periodic torus. This matters for §3.

## 2. What changes and what is reused

### 2.1 Reused unchanged
These lemmas take the width (or an abstract vector `x : V`) as an argument:
- **`BF4WilsonAllNomeShiftedWindowSurvival.lean`:** `window_energy_antitone`,
  `window_telescope`, `window_energy_bound`, **`window_epsBound`**,
  `oneStepEpsBound_one`.
- **`BF4WilsonAllNomeShiftedH1Anchor.lean`:** `OneStepEpsBound`, `shift_norm_pin`,
  `shift_response_pin`, `overlap_expand`, `shifted_energy_telescope`,
  `shifted_tail_overlap_nonnegative`, `shifted_head_overlap_le`,
  `shifted_energy_le_familyResponse`, `shifted_norm_ge_family_response`,
  `shiftedEpsBound_of_relativeFloor`, `NomeScheduleAFCalibrated`,
  `NomeSchedulePhysicalBox`.
- **`BF4WilsonAllNomeGenericNormalizedAnchor.lean`:** **`NormalizedAnchorData`** and all
  its lemmas: `normalizes`, `normalized_norm`, `block_floor`, `mesh_increment_bound`,
  `real_increment`, `real_forward_increment`, `real_floor`. Also `smoothedSector`,
  `smoothedNorm(_pin)`, `smoothedAnchorData`, `smoothedAnchor_macroRatio`,
  `pathKappa_pos`.
- **`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean`:** `block_bernoulli_pow`,
  `floor_of_block_energy`, `macro_ratio_of_twoStep_block(_energy)_general`,
  `block_survival_of_oneStep_energy`, `NomeSchedule`, `side_split`,
  `dyadicPhysicalSpacing`. The B04l interface (`trajectoryDynamicFamily`,
  `PathCubeContraction`) depends only on the schedule.
- **Floors:** `smoothedResponse_ge_family_response`
  (`…ShiftedPaddedNondegenerate.lean:144`, generic in `width qs c hqs`),
  `family_time_geometric_floor` (`BF4WilsonAllNomePlaquetteFamilyBondOrbit.lean:110`,
  needs `base < width` and `faces ⊆ spatialFaces base`), `familyResponseFraction`,
  `varianceFloor`.
- **Schedules:** `afNomeSchedule` and the scalar lemmas in
  `BF4WilsonAllNomeAFPaddedTrajectory.lean` (though see §1.4 on `A`).

### 2.2 Must be redone (stated for `DyadicSmoothedTrajectory`, i.e. for `trajWidth`)
None of these proofs uses `side²` except through `trajWidth_ratio`. They pass
`trajWidth j` as an argument, so the bodies port almost verbatim with `width j` in its
place.
- **Structure and definitions:** the structure itself, plus `familyVector`, `state`,
  `response`, `familyNorm`, `MacroRatioAt`.
- **Path Props and anchors (`…ShiftedH1Anchor.lean`):** `PathShiftedEpsBound` (:396),
  `PathShiftedNondegenerate` (:403), `PathShiftedFamilySurvival` (:407),
  `shiftedPathAnchor` (:468), **`ShiftedAnchorPackage`** (:550).
- **Path theorems (`…ShiftedH1Anchor.lean`):** `pathShiftedEpsBound_iff_response`,
  `pathShiftedEpsBound_of_shiftedFamilySurvival`, `path_shifted_macroRatio`,
  `path_shifted_anchor_floor`, **`path_normalized_anchor_shifted`**,
  `path_normalized_anchor_shifted_of_survival`, `path_shiftedEps_forces_rate`.
- **`…ShiftedWindowSurvival.lean`:** `PathShiftedWindowSurvival`, `PathLagSurvival`,
  `pathShiftedWindowSurvival_of_lagSurvival`,
  **`pathShiftedEpsBound_of_windowSurvival`**,
  **`path_normalized_anchor_of_windowSurvival`**.
- **`…GenericNormalizedAnchor.lean`:** `trajAnchorData`, `pathAnchor`,
  `path_anchor_floor`, `path_normalized_anchor(_with_survival)`. These are needed
  only if the unshifted chain is also wanted.
- **`…ShiftedPaddedNondegenerate.lean`:** **`PathFacesPadded`**, **`paddedNondegFloor`**,
  `paddedNondegFloor_pos`, **`pathShiftedNondegenerate_of_padded`**,
  `path_normalized_anchor_of_windowSurvival_padded`,
  `path_normalized_anchor_shifted_padded`, `paddedZeroMomentumTrajectory` and its
  two corollaries.
- **Optional:** `…H1FixedScale.lean` (the box-kernel H1 path, heuristically false,
  deprioritized) and `PathUnitRatioBridge` / `path_unit_anchor_floor`. These need
  only `side < width`, which `c·side+1` satisfies.

### 2.3 Padding and nondegeneracy, specifically
- **`PathFacesPadded'`:** `faces j ⊆ spatialFaces (c * side j)`, so `base_j = c·side_j`.
  The width lemma replacing `trajWidth_ratio` is `c * side j < c * side j + 1`
  (`Nat.lt_succ_self`). For the zero-momentum family, padding is again
  `fun _ _ hp => hp`.
- **The floor keeps its form:**
  `ρ_j^(2M_j+side_j) · varianceFloor(w_j) · Σ c²`, with
  `ρ_j = familyResponseFraction(w_j, |faces j|)` and `M_j = radiusFactor·side_j`.
  - The exponent `2M_j + side_j` is UNCHANGED, because the time geometry is the same.
  - Only `|faces j|` changes: `O((c·side_j)³)` instead of `O(side_j⁶)`. That changes
    the per-`j` value of `ρ_j`, not its positivity.
  - The A03 consumers use the floor only per `j`, as a positive rational, so no
    uniformity is lost or gained.
- **Nondegeneracy:** the port of `pathShiftedNondegenerate_of_padded` is the same
  `family_time_geometric_floor` application with `base := c * side j`. Trivial.

### 2.4 Window and anchor consumers
- `window_epsBound` is reused as is.
- The port of `pathShiftedEpsBound_of_windowSurvival` keeps its statement: lags
  `side_j/2` and `side_j+1`, and the constraint `(1-θ)·2 ≤ θ·c0`.
- The port of `path_normalized_anchor_of_windowSurvival(_padded)` gives a
  `ShiftedAnchorPackage'` with the same four clauses:
  - unit norm;
  - block floors `κ^i` at lag `i·side_j`;
  - real-time floors through `spacing j`;
  - the geometric increment modulus.
- `NormalizedAnchorData` and A03 are untouched.
- The **meaning** changes. All statements are now about the transfer matrix on a
  fixed spatial box of size about `cL`.

### 2.5 Engineering choice
- **(a) Preferred:** a NEW file with a width-generic structure, e.g.
  `WidthedSmoothedTrajectory`. It would have a field `width : Nat → Nat`, a padding
  base `base : Nat → Nat`, and proofs `side_lt_width`, `base_lt_width`.
  - `width j = c·side j + 1` is one instance.
  - Today's `trajWidth` would be another, giving a consistency check.
- **(b) Rejected:** generalizing `DyadicSmoothedTrajectory` in place. That edits
  verified files and forces a downstream rebuild.

## 3. Window survival in a fixed small physical volume

### 3.1 The statement
On the box of size `cL`, with `R_j(n) = ⟨Y_j, T_j^n Y_j⟩`, the claim is
`θ R_j(side_j/2) ≤ R_j(side_j+1)` for `j ≥ 1`. In physical units that compares
times `L/2` and `L`.

Spectrally, `R_j(n) = ∫ λ^n dμ_j(λ)`. So the claim says the anchor's spectral measure
keeps a θ-fraction of its weight at energies `≲ O(1)/L`.

### 3.2 Heuristic (paper)
- In a small box, weak coupling at scale `L` applies (`g²(L)` small, i.e. `C` large).
- Leading order is a free lattice gauge field in the box.
- The box-smoothed zero-momentum plaquette (time-smoothed over about `L·radiusFactor`)
  has an explicit Gaussian correlator `R^(0)_j`.
- Its ratio at physical times `L` and `L/2` tends to a side-independent `θ_0 > 0`.
  Without smoothing, an infinite-volume dim-8 correlator integrated over space gives
  about `t^{-5}`, i.e. `θ_0 ≈ 2^{-5}`. Smoothing and the finite box only change this
  constant.
- Corrections:
  - `O(g²(L))`;
  - lattice artifacts `O(a_j/L) → 0`;
  - finite-box effects, which are O(1) changes to `θ_0` when the box is about `L`.
- Small-volume spectroscopy (Lüscher 1983; later van Baal) is perturbative and
  consistent with this: lowest energies scale like `g(L)^{2/3}/L`. That is
  physics-level evidence, not constructive control.
- Any `θ > 0` feeds the existing compiler, with larger `c0` and `a`.

### 3.3 What Balaban actually controls (confidence level stated)
- Balaban's CMP series (mid-1980s) on renormalization-group analysis of 4D lattice
  gauge theory (Wilson-type actions) gives, in a FIXED finite physical volume (a
  periodic torus) as `a → 0`:
  - **ultraviolet stability**: upper and lower bounds on the partition function,
    `e^{−K·vol} ≤ Z ≤ e^{K·vol}`-type, uniform in the spacing;
  - an RG sequence of **effective actions** on coarser lattices, with a
    small-field/large-field decomposition; small-field effective actions are
    controlled (analytic, local), and large-field regions are suppressed.
- I am confident of this level of description. I do not cite specific theorem
  numbers.
- As far as I know, Balaban does NOT:
  - construct the continuum limit of correlation functions;
  - give LOWER bounds on specific gauge-invariant correlators;
  - say anything about transfer-matrix spectral weight;
  - treat lattice-scale composite observables like the plaquette / `tr F²`.
- Related work:
  - Dimock's expository series ("The renormalization group according to Balaban")
    reworks the method in simpler settings.
  - Magnen–Rivasseau–Sénéor (CMP 1993, "Construction of YM4 with an infrared cutoff")
    is, as I understand it, a continuum, gauge-fixed construction with an IR cutoff.
    It is the closest result about correlation functions. It is not lattice, not the
    heat-kernel action, and not gauge-invariant composite operators in a
    transfer-matrix (OS) picture.

### 3.4 The bridge (none of this exists)
- **B1. Observables in the RG.** Balaban-type bounds for the generating function
  `Z(J)/Z(0)`, with sources coupled to the smoothed plaquette at two time slabs.
  Analyticity in `J`, uniform in `a`. That gives only UPPER bounds on connected
  correlators (Cauchy estimates).
- **B2. Leading-order asymptotics with remainder: the real new theorem.** The claim:
  `R_j(n) = R^(0)_j(n)·(1 + ε_j(n))`, with `|ε_j(n)| ≤ C·g²(L)` uniformly in `j`, for
  `n ∈ {side_j/2, side_j+1}`.
  - This is the LOWER-bound mechanism.
  - It requires controlled renormalization of the composite operator. Multiplicative
    `Z` cancels in the ratio; mixing with the identity is removed by centering.
  - It amounts to a constructive finite-volume continuum limit for composite-operator
    correlators. That is research-level, comparable in scope to extending Balaban's
    program, and not Lean-scoped.
- **B3. The free computation.** `R^(0)_j(side_j+1)/R^(0)_j(side_j/2) ≥ 2θ_0 > 0`,
  uniformly in `j`. This is an explicit lattice-Gaussian computation in the box.
  Plausible and moderate in effort, but in Lean it would need lattice Fourier
  analysis the repo does not have.
- **B4. Setting.** Balaban's setting is a periodic torus with a Wilson action and
  finite time extent. The repo has a free spatial boundary (§1.5), the heat-kernel
  action, and infinite time (completed OS carrier). Three things are needed:
  - the heat-kernel action must be inside the class the RG handles (plausible, not
    checked);
  - a boundary-condition comparison;
  - the time-extent → ∞ identification of `R_j(n)` with torus correlators, with
    uniformity.

### 3.5 Verdict
- B1 + B2 + B3 + B4 ⇒ window survival with `θ = θ_0(1 − O(g²(L)))` for `L` small
  enough.
- Balaban's results make the fixed-volume statement **plausible and well-posed in a
  regime where constructive methods exist**. They do not imply it.
- B2 is the missing theorem.
- In Lean, window survival stays an OPEN Prop on the fixed-volume carrier, exactly
  as today.

## 4. Infinite volume: the hard part moves; it is not removed

### 4.1 What fixed-volume A03 says
At each `j`, there is a normalized anchor in the box `cL` with block floors `κ^i` at
physical times `iL`. These are **lower** bounds on correlations.

A mass gap is an **upper** bound: `R(t) ≤ C e^{−m t}` with `m > 0`, uniform in `a`
**and** in volume. The A03 floors bound the decay from the wrong side; at most they
give `gap ≤ −log κ / L`. So:
- **the fixed-volume A03 conclusion says nothing about the infinite-volume gap**;
- it is only consistent with the expected small-box spectrum `E ~ g(L)^{2/3}/L`;
- the same holds for today's carrier: A03 floors alone are not a gap statement in
  either volume.

### 4.2 What is still needed
The thermodynamic limit `L → ∞` in units of `Λ⁻¹`:
- control uniform in `L` as `g(L)` grows into the strong-coupling regime (the IR
  problem: large fields, confinement);
- existence of the infinite-volume continuum theory;
- a gap uniform in volume.

This is where the real mass-gap difficulty sits. Balaban-type small-field control
does not reach it.

### 4.3 Where the difficulty sits on each route
- **Today's carrier (width `side²+1`, physical width `side·L → ∞`).** Window survival
  already demands uniform control in a growing physical volume. The IR is buried
  inside the open Prop.
- **Fixed volume.** The open Prop becomes a UV statement (§3), but a separate IR
  limit must be added afterwards. The hard part moves; it is not removed.

## 5. Size / risk table

### 5.1 Lean (new files only, no edits to existing ones)

| step | content | rough lines | risk |
|---|---|---|---|
| FV1 | `WidthedSmoothedTrajectory` structure (width, base, `side_lt_width`, `base_lt_width`), `familyVector`/`state`/`response`/`familyNorm`; instances `c·side+1` and (check) `trajWidth` | 120–180 | low |
| FV2 | ports of the `…ShiftedH1Anchor` path layer: `PathShiftedEpsBound'`, `PathShiftedNondegenerate'`, `shiftedPathAnchor'`, `ShiftedAnchorPackage'`, `path_shifted_macroRatio'`, `path_shifted_anchor_floor'`, `path_normalized_anchor_shifted'` | 250–350 | low math; medium elaboration (large four-clause package term, heartbeats) |
| FV3 | ports of the `…ShiftedWindowSurvival` path part and the `…ShiftedPaddedNondegenerate` path part: `PathShiftedWindowSurvival'`, `pathShiftedEpsBound_of_windowSurvival'`, `PathFacesPadded'`, `paddedNondegFloor'`, `pathShiftedNondegenerate_of_padded'`, `path_normalized_anchor_of_windowSurvival_padded'` | 120–180 | low |
| FV4 | concrete instance: zero-momentum faces on `spatialFaces (c*side j)`, schedule with `A ≈ 1942/1000` (re-proving `NomeScheduleAFCalibrated` with the new constant) or reusing `afNomeSchedule`; headline `fv_path_normalized_anchor_of_windowSurvival` | 60–200 | low (numerics fiddly) |
| total | | **≈ 550–900** | 5–7 monitored single-file checks |

### 5.2 Not Lean-scoped (paper / research)

| item | content | risk |
|---|---|---|
| B1 | RG bounds with observable sources (upper bounds only) | high |
| B2 | leading-order correlator asymptotics with uniform remainder in fixed volume | **very high; research-level; the riskiest lemma overall** |
| B3 | free lattice-Gaussian ratio `≥ 2θ_0` in the box | moderate (paper); high in Lean (no lattice Fourier analysis in the repo) |
| B4 | torus / Wilson / finite-time versus free-boundary / heat-kernel / OS-carrier comparison | medium–high |
| IR | thermodynamic limit and uniform gap | the Clay core; open |

### 5.3 Riskiest lemmas
- **In Lean:** the `path_normalized_anchor_shifted'` / `ShiftedAnchorPackage'` port.
  The risk is elaboration size, not mathematics.
- **Overall:** B2 (`fixedVolume_correlator_asymptotics`, a placeholder name). Without
  it, window survival in fixed volume stays open.

## 6. Recommendation

### 6.1 Not a better critical path for the gap
- The Lean work is mechanical and adds no mathematical content. It re-states the same
  open Prop on a different carrier.
- The Prop is still unproved there: it needs B1–B4, and B2 is research-level.
- The infinite-volume gap gets no closer (§4).

### 6.2 But a better-posed home for the open input
- In a fixed small box, window survival is a UV statement in the regime where
  constructive RG methods exist, with an explicit leading-order prediction `θ_0 > 0`.
- On today's carrier the same Prop secretly contains IR control.
- If the project wants its "OPEN" list to name the most plausible statement, this is
  it. That is a documentation/framing gain, not progress toward the gap.

### 6.3 Timing: AFTER darthur's F1–F4 decision, not now
1. `PLAN-SPATIAL-SMEARED-ANCHOR-2026-10-06.md` F4 already proposes a new trajectory
   with its own width schedule (`ExprAnchorTrajectory`). Doing FV1–FV3 now and F4
   later would duplicate the same path-theorem ports. One width-generic trajectory
   (FV1) should serve both.
2. **Compatibility tension.** The smeared anchor uses `n_j ≈ (ρ side_j)²/(cα)` staple
   steps, and its `physical`/padding lemma needs the loop at distance `≥ n_j` from the
   window edge. That means width `≳ side_j²` for exact (untruncated) smearing, which
   does NOT fit `c·side_j + 1`.
   - So the F decision constrains whether a fixed-volume carrier is even compatible
     with the anchor.
   - Possible ways around it: truncated smearing, `n_j ∝ side_j` with a different
     smearing kernel, or a periodic box. Each is a separate design decision.
3. The `A` recalibration (`≈1.942`, §1.4) should be folded into the same step rather
   than done as a separate edit.

### 6.4 Nothing urgent now
If darthur wants a tiny Lean step before the F decision, the only candidate is the
recalibrated schedule (`A ≈ 1942/1000`). That is a new file and needs its own
approval. It does not change any conclusion.
