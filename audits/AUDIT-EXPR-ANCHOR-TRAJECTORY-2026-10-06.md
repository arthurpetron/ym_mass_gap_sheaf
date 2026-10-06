# Audit: expression anchor trajectories (second-anchor plan, low-risk additive part)

Date: 2026-10-06 (PT). Status: ADDITIVE. `Y_j` and every existing theorem are untouched.
Only new files were added, plus import lines in `lean/YMGap.lean`.

Scope (YM Bot decision, 2026-10-06):
* P8 cannot resolve window survival on the exact `Y_j` by MC. The plaquette overlap is
  about 1.5-3.5%, and every measured W is consistent with 0.
* The NS-k2 smoothed loop gives a clean W of about 0.15-0.35.
* So the anchor/path/window/package layer is generalized to an ARBITRARY slab
  `IntrinsicExpression` family.
* NOT started: the NS smearing word (F1/F2), and the H-var/H-ray proofs for any
  smeared loop. FV1-FV4 and G1-G8 remain held. The anchor-swap restatement remains held.

## §1 `BF4WilsonAllNomeExprAnchorTrajectory` (structure, Props, nondegeneracy, window)

Generic, for any `ψ : IntrinsicExpression width`. Let `x = centeredExcitation ψ` and
`Y_M = orbitSum x (timeKernel M)`, the one-sided box with lags 0..M. Then:
* `exprResponse_orbit_expand`, `exprResponse_pin`: the response is pinned to
  `centeredTimeMoment (m+k+n) ψ ψ`.
* `exprResponse_ge_vector_response`: `B(x,T^(2M+n)x) ≤ R_M(n)`.
* `exprResponse_floor`: if `0 ≤ ρ`, `v ≤ B(x,x)` and `ρB(x,x) ≤ B(x,Tx)`, then
  `ρ^(2M+n)·v ≤ R_M(n)`.

`structure ExprAnchorTrajectory`:
* `schedule : NomeSchedule`;
* `width : Nat → Nat`, generic, which is the structure FV1 would need;
* `radius : Nat → Nat`;
* `expr : (j : Nat) → IntrinsicExpression (width j)`.

The anchor block stays the dyadic `side j = 2^j` with spacing `2^-j`. The package's
real-time rows and block split use exactly this.

OPEN Props:
* `ExprHVar tr v`: for all j, `0 < v j` and `v j ≤ B(x_j,x_j)`.
* `ExprHRay tr ρ`: for all j, `0 < ρ j` and `ρ_j B(x_j,x_j) ≤ B(x_j, T x_j)`.
* `ExprShiftedEpsBound tr c0`: the shifted H1 on `T^(side_j/2) Y_j`.
* `ExprShiftedWindowSurvival tr θ`: for j ≥ 1, `θ R_j(side_j/2) ≤ R_j(side_j+1)`.

Qualitative: `ExprShiftedNondegenerate tr fl`, i.e. `fl_j ≤ R_j(side_j)`.

Proved:
* `exprShiftedNondegenerate_of_hvar_hray`, with **floor
  `fl_j = ρ_j^(2·M_j + side_j) · v_j`** (`exprNondegFloor`).
  * Exponent check: the shifted anchor needs a floor at lag `n = side_j`, because
    `B(T^h Y, T^h Y) = R_Y(2h)` with `2h = side_j` for j ≥ 1.
  * The Jensen/antitone step costs `2M_j` more lags. So the exponent is
    `2M_j + side_j`, which matches `paddedNondegFloor`.
* `exprShiftedEpsBound_iff_response`.
* `exprShiftedEpsBound_of_windowSurvival`, under `0 < θ ≤ 1`, `2(1-θ) ≤ θc0` and
  `1 ≤ c0`.

## §2 `BF4WilsonAllNomeExprShiftedAnchorPackage` (the A03 package for an expression anchor)

This copies `smoothedAnchorData` / `shiftedPathAnchor` / `ShiftedAnchorPackage`, replacing
`familyState` with an arbitrary `ψ` and `trajWidth j` with `tr.width j`. Contents:
* `exprStream`, `exprSector`, `exprSector_pin`: the range witness for `T(s)Y_M(ψ)`.
* `exprNorm`, `exprNormCauchy`, `exprNorm_pin`: a concrete Cauchy representative of
  `R_M(n)` built from `centeredTimeMoment (m+k+n) ψ ψ`.
* `exprAnchorData`: `NormalizedAnchorData` at any block `s ≥ 1`.
* `exprShiftedPathAnchor`, `expr_shifted_macroRatio`, `expr_shifted_anchor_floor`,
  `ExprShiftedAnchorPackage`, `expr_normalized_anchor_shifted`.
* `expr_normalized_anchor_of_windowSurvival`.
* **`expr_normalized_anchor_of_windowSurvival_hvar_hray`**: gives
  `ExprShiftedAnchorPackage tr δ hδ a (exprNondegFloor tr v ρ) _`. It assumes:
  * the OPEN inputs `ExprShiftedWindowSurvival tr θ`, `ExprHVar tr v` and `ExprHRay tr ρ`;
  * the scalar side conditions `1 ≤ a`, `0 < θ ≤ 1`, `(1-θ)·2 ≤ θ c0`, `1 ≤ c0`,
    `0 ≤ δ < 1` and `c0 ≤ 2^a δ`.

The package says that for every `j ≥ a`, the normalized anchor `α_j T^(side_j) Y_j`
has all four of:
* unit norm;
* block floors `κ^i` at lag `i·side_j`;
* real-time survival `κ^(i+1)`;
* the geometric real-time increment modulus.

Here `κ = (1-δ)^(2^a)`.

## §3 `BF4WilsonAllNomeExprAnchorRegression` (no-regression)

`toExprTrajectory tr` maps a trajectory to the expression trajectory with
`width := trajWidth`, `radius := tr.radius` and
`expr j := familyState (trajWidth j) (faces j) (coeff j) _`.

* DEFINITIONAL (`rfl` / `Iff.rfl`, all accepted by the kernel):
  * vector, state and response;
  * `ExprShiftedEpsBound ↔ PathShiftedEpsBound`, `ExprShiftedWindowSurvival ↔
    PathShiftedWindowSurvival` and `ExprShiftedNondegenerate ↔ PathShiftedNondegenerate`;
  * `exprShiftedPathAnchor (toExpr tr) = shiftedPathAnchor tr`;
  * `ExprShiftedAnchorPackage (toExpr tr) ↔ ShiftedAnchorPackage tr`;
  * `exprNondegFloor (toExpr tr) paddedVar paddedRho = paddedNondegFloor tr`.
* H-var and H-ray DISCHARGED for plaquette trajectories:
  * `toExpr_hvar` (every trajectory), via `familyExcitation_norm_floor`, with
    `v_j = varianceFloor(w_j)·Σc_j²`;
  * `toExpr_hray` (padded trajectories), via `family_rayleigh_floor`, with
    `ρ_j = familyResponseFraction(w_j,|faces_j|)`.
* `padded_nondegenerate_via_expr` and `padded_package_via_expr` reprove
  `pathShiftedNondegenerate_of_padded` and
  `path_normalized_anchor_of_windowSurvival_padded` through the general layer.
* Concrete instances: `paddedZeroMomentumExpr` and `afPaddedZeroMomentumExpr`, each
  with H-var and H-ray.
* NOT ported: `BF4WilsonAllNomeWindowGapCompatibility`. Optional; deferred.

## Build record (box, 2026-10-06 PT)

The Mac was at kern pressure level 2 for more than an hour, so no Lean ran on the Mac.

Setup:
* Fresh checkout of `codex/full-workspace-snapshot-2026-07-24` @ 673c0962 on the box,
  made from a git bundle of the Mac checkout. The box has no GitHub credentials.
* Import closure of the three files: 3286 repository modules.
* Their existing build artifacts (olean/ilean/trace/hash/ir) were copied from the Mac's
  `.lake/build` for exactly these modules. They were accepted only through Lake's own
  trace check: `safe_lean_build.py ... -- --no-build +…:olean` reported all three direct
  imports up to date, which validates the source hashes and the toolchain v4.29.1 commit
  f72c35b3. No upstream module was rebuilt.
* Built only the three new modules, via `scripts/safe_lean_build.py --jobs 1
  --reserve-gib 2 --lake-worker-limit-gib 4`. Settings: `LEAN_NUM_THREADS=1`,
  `nice -n 10`, a process-group timeout of 1800 s, a 10 s sampler, and abort if
  MemAvailable < 2 GiB.

Results:
* File (i): ~10 s. Files (ii)+(iii): ~20 s.
* All exits 0; no warnings; compiled unchanged from the drafts.
* Axioms: every theorem and def is `[propext, Quot.sound]`; the structure
  `ExprAnchorTrajectory` uses none.
* `scripts/lean_forbidden_token_scan.py`: 0 hits.
