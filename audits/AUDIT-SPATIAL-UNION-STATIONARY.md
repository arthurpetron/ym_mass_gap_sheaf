# Spatial union centering and stationary sector

Date: 2026-09-16. Baseline: `a90f0e1`.

Whole-project goal: nontrivial continuum quantum Yang--Mills on R^4 for each
compact simple gauge group, the required QFT axioms, and a positive physical
Hamiltonian gap, within the constructive witness/axiom contract. That goal
remains open. This checkpoint concerns the existing small-nome, fixed-spacing
SU(2) spatial presentation completion.

## Checked result and causal proof

1. **Actual rational operations.** Common-base transport supplies dense
   bilinearity and squared-distance estimates. The existing explicit-modulus
   completion maps then act on the SAME `UnionCompletion`:
   `lean/YMGap/Continuum/BF4SpatialUnionLinear.lean:173`, `distSq_add`;
   `:191`, `distSq_smul`; `:203`, `addition`; `:207`, `scalarContinuous`;
   `:241`, `completedAdd`; `:245`, `completedSmul`.
2. **Separation without circular algebra.** The actual difference-pairing
   limit controls the original streams' distance through
   `lean/YMGap/Continuum/BF4SpatialUnionLinear.lean:106`, `distance_difference`.
   `lean/YMGap/Continuum/BF4SpatialUnionBilinear.lean:151`,
   `closeOfDifferenceZero`, constructs Type-valued closeness with the existing
   difference-stream pairing rate. `:169`, `completedSub_norm_zero_iff`, and
   `:180`, `completed_eq_of_pairings`, establish separation BEFORE deriving
   group laws. The completed bilinear laws start at `:93`,
   `completedInner_add_left`. The rational laws are proved in
   `lean/YMGap/Continuum/BF4SpatialUnionLinearLaws.lean:42`,
   `completedAdd_assoc`, through `:108`, `completedTime_smul`.
3. **Constructed unit projection.** Rational multiples of the actual unit
   have exact coefficient-square distance:
   `lean/YMGap/Continuum/BF4SpatialUnionUnitProjection.lean:104`,
   `unitMultiple_distance`. The actual unit coefficient and its supplied
   approximation modulus produce `scalarUnitCauchy` (`:125`),
   `unitCoefficientCauchy` (`:142`), and `unitProjectionCauchy` (`:166`).
   Pairing separation proves quotient descent to `unitProjection` (`:184`).
   Its exact formula is `unitProjection_pairing` (`:192`):
   `B(P x,y) = B(x,U) * B(U,y)`.
4. **Same-object centered correlations.**
   `lean/YMGap/Continuum/BF4SpatialUnionCentered.lean:44`, `center`, subtracts
   this projection. `center_mk` (`:49`) pins the actual Cauchy stream;
   `centeredState` (`:136`) targets the already existing unit complement,
   not a new subtype. `centered_inner` (`:108`) and
   `orthogonal_decomposition_inner` (`:114`) give exact mixed Pythagoras.
   `centered_time_pairing` (`:149`) identifies every centered time pairing
   with the existing `completedCenteredScalar` on the same B, U and T.
5. **Stationarity contracts to the unit projection.**
   `lean/YMGap/Continuum/BF4SpatialUnionUnitComplement.lean:84`,
   `fixed_twoStep_complement_eq_zero`, already excludes stationary vectors
   in the complement. Centering now commutes with actual physical time
   (`lean/YMGap/Continuum/BF4SpatialUnionCentered.lean:143`,
   `completedTime_center`), so that theorem applies to every stationary
   vector's centered part. `center_decomposition` (`:81`) completes the proof:
   `lean/YMGap/Continuum/BF4SpatialUnionStationary.lean:46`,
   `fixed_twoStep_iff`, proves `T_2 x=x iff P x=x`;
   `:61`, `fixed_oneStep_iff`, and `:71`, `fixed_all_time_iff`, give the
   corresponding one-step and all-discrete-time statements.

Stationary vectors are uniquely determined by their actual RC unit coefficient:
`lean/YMGap/Continuum/BF4SpatialUnionStationary.lean:80`,
`stationary_coefficient_unique`. Unit overlap ONE forces equality to the unit
(`:94`, `stationary_unit_overlap_one`). Overlap one is not merely norm one.

## Explicit witnesses and parameter boundary

- Addition retains `max(M_X(epsilon/4), M_Y(epsilon/4))`:
  `lean/YMGap/Continuum/BF4SpatialUnionLinear.lean:232`, `addCauchy_modulus`.
- Rational scaling retains `M_X(epsilon/(c*c+1))`: same file `:237`,
  `smulCauchy_modulus`; the tolerance is defined by
  `lean/YMGap/Continuum/BF4ExactSlabPlaquetteCompletionLinear.lean:55`,
  `scalarTolerance`.
- Unit multiples retain the supplied scalar modulus at `min(epsilon,1)`:
  `lean/YMGap/Continuum/BF4SpatialUnionUnitProjection.lean:134`,
  `scalarUnitCauchy_modulus`; tolerance definition:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointCenteredStream.lean:32`,
  `centerTolerance`.
- Arbitrary input streams may have unbounded support bases. Only the computed
  unit-multiple output stream has constant base 1. This does not impose a
  support bound on the input.
- All physical theorems retain the existing five guards: `0<w`, `w<1`,
  `heatRatio w<=1/2`, `heatRemainderBound w<1`, and
  `entropyRate 625 (adjustedCoreRate w hd)<1`. The contraction rate is unchanged.
  The prior `1/1024` instance supplies these guards; no new uniformity in beta
  or lattice spacing is asserted.

No vector or scalar representative is selected from a quotient. For a supplied
Cauchy representative the coefficient and QCauchy data are explicit; for an
arbitrary quotient vector the coefficient is an RC and projection is descended
directly. The stationary theorem characterizes the constructed projection
image; it does not return a chosen Type-valued real scalar for every vector.

## Next actual consumer; unproved work

Source-reviewed plan only: construct completed squared distance
`B(x-y,x-y)`, prove its representative limit and dense approximation with the
given `X.modulus`, then construct diagonal limits of supplied Cauchy rows.
Closest existing templates:

- `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedApproximation.lean:50`,
  `constantApproximation_bound`, and `:58`, `approximationData`.
- `lean/YMGap/Continuum/BF4ExactSlabThermodynamicCauchyRows.lean:48`,
  `CauchyRows`; `:94`, `diagonalCauchy`; `:102`, `rowLimitRate`; `:147`,
  `rowLimit_independent`; `:169`, `rowLimit_presentationRows`.

The concrete subsequent consumer is a reduced resolvent of the SAME T_2, with
computed partial-sum representatives. The existing template is
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolvent.lean:65`,
`resolventRepresentative`, through `:171`, `solutionCertificate`. These are
different-carrier theorems, NOT union instances. Generic extraction must retain
an old-instance pin and supply all union inputs.

Rate warning: `lean/YMGap/Continuum/BF4ExactSlabThermodynamicResolventPartial.lean:105`,
`partial_norm_bound`, uses the old fixed numerical decay to get constant 4.
It cannot simply be copied for arbitrary current q<1. The proposed replacement
is a rational weighted-triangle argument with squared-norm ceiling
`(1-q)^(-2)*B(Cx,Cx)` and tail `q^(2m)` times that ceiling. This estimate is NOT
proved in this checkpoint. The available scalar modulus template is
`lean/YMGap/Continuum/PositiveContractionResidual.lean:119`, `geometricCutoff`,
and `:126`, `geometric_bound`.

Supplied-row completion suffices for that proposed construction; no lift of an
arbitrary `Nat -> UnionCompletion` sequence is supplied. Full real-scalar
structure, arbitrary quotient-sequence metric completeness, full gauge
observable coverage and spatial translations, Hilbert/OS/QFT identification,
continuous time/Hamiltonian, physical normalization and continuum passage,
continuum nontriviality and every compact simple group remain open. The existing
AF small-nome-guard obstruction is unchanged. No new same-action scale/volume
estimate or canonical Clay-facing field has been discharged here.

## Verification

Six focused serialized checks used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check ... --check-output ...`. Every run had a fresh
process/swap preflight. All handles are terminal. No root/full-tree/full audit
ran; six root imports were added. No safety threshold changed; CI stays manual.

Final logs (SHA256; all under `/tmp/`):

- `ym-union-linear-20260916.log`: 24 gates;
  `559660b952f2cfd68cf8a0b4619d2e20b24dd3ae7828cfe15808a60096f71701`.
- `ym-union-bilinear-20260916.log`: 29 gates;
  `a787938a8ba900243ad648555369ff11ba5e5aad7323af366f6d9b0c55ccc94d`.
- `ym-union-linear-laws-20260916.log`: 9 gates;
  `e57eca23808a9ef9664bd3be4c96c35d8577dfe996d4d94273c2da33bdc3d73c`.
- `ym-union-projection-20260916.log`: 27 gates;
  `feb938c94723159281a6147c7b2f07b8d9c4bf74f3dfc3dd1a3fe036c034e765`.
- `ym-union-centered-20260916.log`: 20 gates;
  `bc0b1b0d40eee9c8c68be894f733184f687a16a71d3bedc21866f28c23a9bd59`.
- `ym-union-stationary-20260916.log`: 5 gates;
  `371059ca7a69f6353ddfd0d8b29f5a93ae2c4e38d75524c70982e0e160dab918`.

Total: 114 public gates, only {propext, Quot.sound}; final logs contain no error,
warning, sorryAx or classical/native dependency. The first linear check had two
unused simp warnings, removed and rechecked. The first bilinear attempt failed
on local-notation field syntax; parenthesizing that notation fixed the check.
No source hole, existing theorem, canonical field, axiom or analytic premise
changed. Independent source review found no same-object, circularity, explicit
modulus, or stationarity-scope defect. No routine literature scan was run.
