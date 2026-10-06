# Audit: `PathShiftedNondegenerate` for the current `Y_j` under padding (2026-10-06)

Lean: `lean/YMGap/Continuum/BF4WilsonAllNomeShiftedPaddedNondegenerate.lean`.
Status: PROVED for the current anchor `Y_j` (box-smoothed coherent plaquette
family) under the padding hypothesis `PathFacesPadded tr`. No anchor edit.
Axioms {propext, Quot.sound}; no sorry. Window survival remains the frontier.

## (1a) The floor is used per j only

Read from the exact statements (`BF4WilsonAllNomeShiftedH1Anchor.lean`,
`BF4WilsonAllNomeShiftedWindowSurvival.lean`,
`BF4WilsonAllNomeGenericNormalizedAnchor.lean`):

- `PathShiftedNondegenerate tr fl := ∀ j, RCle (Rq (fl j)) (tr.response j (side j))`
  is pointwise in `j`.
- `path_shifted_macroRatio` uses `Hnd j` only to build the norm floor
  `fl j ≤ B(T^(side_j/2)Y_j, T^(side_j/2)Y_j)` and passes `(fl j) (hfl j)` to
  `block_survival_of_oneStep_energy`. Its conclusion
  `κ R_j(side_j) ≤ R_j(2 side_j)`, `κ = (1-δ)^(2^a)`, does not involve `fl`.
- `shiftedPathAnchor` puts `κ·fl_j` into `NormalizedAnchorData.floor`, which
  feeds only the constructive inverse square root (`normalizer`) and must be a
  TRUE floor (`path_shifted_anchor_floor`, again per j via `Hnd j`).
- `ShiftedAnchorPackage` concludes: unit norm, block floors `κ^i`, real-time
  floors `κ^(i+1)`, and the geometric increment modulus. None of these
  mentions the size of `fl j`. `fl` enters only as a parameter that indexes
  which normalizer was built.
- `path_normalized_anchor_of_windowSurvival` and
  `path_normalized_anchor_shifted_of_survival` pass `Hnd` through unchanged.
- `path_shiftedEps_forces_rate` uses `hfl j` and `Hnd j` only through
  `sh_coeff_le_of_scale_le` (division by a positive number).
- No other file in `lean/YMGap` consumes `PathShiftedNondegenerate`,
  `ShiftedAnchorPackage` or `shiftedPathAnchor` (rg).

Finding: nothing requires a j-uniform lower bound. A floor that decays
exponentially in `side_j` discharges the Prop. `Σ c²` comes for free from the
existing variance floor, so no single-`c_k²` reduction was needed.

## Statements

```lean
def PathFacesPadded (tr : DyadicSmoothedTrajectory) : Prop :=
  ∀ j p, p ∈ tr.faces j → p ∈ spatialFaces (side j * side j)

def paddedNondegFloor (tr : DyadicSmoothedTrajectory) (j : Nat) : Q' :=
  familyResponseFraction (tr.schedule.nome_pos j) (tr.schedule.nome_lt_one j)
      (tr.faces j).length ^ (2 * tr.radius j + side j) *
    (varianceFloor (tr.schedule.nome j) (tr.schedule.nome_pos j) *
      listQSum (fun face => tr.coeff j face * tr.coeff j face) (tr.faces j))

theorem paddedNondegFloor_pos (tr) : ∀ j, (0 : Q') < paddedNondegFloor tr j

theorem smoothedResponse_ge_family_response (M n : Nat) :   -- generic carrier
    RCle (B x0 (T (2*M+n) x0)) (smoothedResponse hw0 hw1 width qs c hqs M n)

theorem pathShiftedNondegenerate_of_padded (tr) (hpad : PathFacesPadded tr) :
    PathShiftedNondegenerate tr (paddedNondegFloor tr)

theorem path_normalized_anchor_of_windowSurvival_padded (tr) (c0 theta delta) (a) ...
    (hpad : PathFacesPadded tr) (Hw : PathShiftedWindowSurvival tr theta) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr)

theorem path_normalized_anchor_shifted_padded (tr) (c0 delta) (a) ...
    (hpad : PathFacesPadded tr) (H1s : PathShiftedEpsBound tr c0) :
    ShiftedAnchorPackage tr delta hdelta a (paddedNondegFloor tr) (paddedNondegFloor_pos tr)

def paddedZeroMomentumTrajectory : DyadicSmoothedTrajectory   -- concrete instance
theorem paddedZeroMomentum_padded : PathFacesPadded paddedZeroMomentumTrajectory
theorem paddedZeroMomentum_nondegenerate :
    PathShiftedNondegenerate paddedZeroMomentumTrajectory
      (paddedNondegFloor paddedZeroMomentumTrajectory)
```

Here `ρ_j = familyResponseFraction(w_j, N_j) = w_j^12 (localLower(w_j,4N_j)/localUpper(w_j,4N_j))²`,
`N_j = |faces j|`, `M_j = tr.radius j = radiusFactor·side_j`. The floor is

  `ρ_j^((2·radiusFactor + 1)·side_j) · varianceFloor(w_j) · Σ_p c_j(p)²`.

## Proof chain (scale j, `width = trajWidth j = side_j² + 1`)

1. `familyExcitation_norm_floor` (needs only `faces_spatial`, `faces_nodup`):
   `varianceFloor(w_j)·Σc² ≤ B(x,x)`, `x = familyExcitation`.
2. Scale by `ρ_j^L ≥ 0`, `L = 2M_j + side_j`.
3. `family_time_geometric_floor` with `base = side_j²`, `hwidth = trajWidth_ratio j`
   (`side_j² < side_j² + 1`) and `hqs = hpad j`: `ρ^L B(v,v) ≤ B(v,T^L v)`.
   Here `v = centeredVector (familyState …)` is definitionally `x` (proof
   irrelevance for the face-inclusion argument).
4. `smoothedResponse_ge_family_response M_j side_j`: `R_x(2M_j + side_j) ≤ R_Y(side_j)`.

## Shift-constant check

`timeKernel M = boxKernel (1/(M+1)) M`, and `boxKernel r M` lists lags
`M, M-1, …, 0`: it is ONE-SIDED (lags `0..M`), not symmetric.
`smoothedResponse_orbit_expand` gives
`R_Y(n) = Σ_{m≤M} Σ_{k≤M} (M+1)^(-2) R_x(m+k+n)`. The maximal lag is exactly
`2M+n`. Each term satisfies `R_x(2M+n) ≤ R_x(m+k+n)` by
`response_le_of_le hw0 hw1 width x0 (h : m+k+n ≤ 2M+n)`, which states
`B x (T b x) ≤ B x (T a x)` for `a ≤ b` (antitone, correct direction).
`boxSum_ge_const` twice plus `timeKernel_mass M ≈ 1` gives
`R_x(2M+n) ≤ R_Y(n)`. With `n = side_j`, the lag is
`2·radiusFactor·side_j + side_j`. This is the lag-`n` generalization of the
existing `smoothedCoherent_norm_ge_family_response` (`n = 0`, lag `2M`).

## (1b) Padding is satisfiable

No concrete `DyadicSmoothedTrajectory` existed in the repo (rg for
`DyadicSmoothedTrajectory where` / `.mk`: none). A minimal concrete instance
was constructed and checked:

- `schedule := dyadicNomeSchedule` (`w_j = 1 - 2^-(j+1)`), `radiusFactor := 1`;
- `faces j := spatialFaces (side_j * side_j)`: every spatial plaquette of the
  padded interior box. This is the zero-momentum sum over `[0, side_j²)^3`
  at time 0, i.e. one layer inside the carrier `trajWidth j = side_j² + 1`;
- `coeff := 1`; `faces_spatial` by `spatialFaces_mono` (`side² ≤ side²+1`);
  `faces_nodup` by `spatialFaces_nodup`; `coeff_mass_pos` because the
  origin `(x0,x1)` plaquette is in the list (`origin_face_mem`).
- `paddedZeroMomentum_padded` holds by `fun _ _ hp => hp`.

Width/padding rule: `hpad` holds iff every face has spatial base-point
coordinates `< side_j²` (`spatialFaces_mem_iff`), i.e. stays at least one
lattice layer from the far face of the `trajWidth j = side_j² + 1` carrier.
Any family built in `spatialFaces s` with `s ≤ side_j²` qualifies, for example
families of Wilson-square scale `side_j` (`spatialFaces_mono`). It FAILS for
the full-width zero-momentum family `spatialFaces (trajWidth j)` (the
`zeroMomentumSmoothedState` pattern at `width = trajWidth j`), whose outermost
layer is unpadded. Padding is a hypothesis on the trajectory data, not a
change to the anchor's definition.

## Honest scope

- This closes `PathShiftedNondegenerate` for the current `Y_j` under
  `PathFacesPadded`. It is qualitative: `ρ_j^((2m+1) side_j)` decays
  exponentially in `side_j` (and `ρ_j` itself depends on `N_j`).
- It gives NO information on window survival. The only survival ratios
  this floor technology yields have the form `ρ_j^(O(side_j))`, which collapse
  exponentially. `PathShiftedWindowSurvival`
  (equivalently `PathShiftedEpsBound`) remains the single OPEN quantitative
  input. With padding, `path_normalized_anchor_of_windowSurvival_padded` needs
  only `Hw` and `hpad`.
- G1–G8 (generic floors for a smeared anchor) are ON HOLD pending darthur's
  decision on the anchor switch.

## Checks

One monitored single-file check (`safe_lean_build.py --jobs 1
--check-worker-limit-gib 8`, `LEAN_NUM_THREADS ≤ 2`, 10 s sampler, guard):
exit 0, no warnings, ~11 s. Axioms of all 11 printed declarations:
`[propext, Quot.sound]` (`PathFacesPadded`: `[propext]`). Forbidden-token
scan: 0 hits.
