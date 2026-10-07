# Decision: interacting response shape, not bare heat smoothing (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms and
a finite positive physical Hamiltonian mass gap.

## Selected mathematical increment before verification

The actual response is the box-smoothed original centered covariance, not a
bare heat correlation. The current consumer is
`BF4WilsonAllNomeShiftedWindowSurvival.pathShiftedEpsBound_of_responseArea`.
Its AF-family area input remains unsupplied. No additional assuming-the-area
structure is proposed.

The consumer is at
`lean/YMGap/Continuum/BF4WilsonAllNomeShiftedWindowSurvival.lean:490`.
The actual covariance expansion is
`lean/YMGap/Continuum/BF4WilsonAllNomeSmoothedCoherentState.lean:326`,
`smoothedResponse_orbit_expand`, with the original moment pin at line 341,
`smoothedResponse_pin`.

Two useful tests/estimates are selected:

1. Construct an explicit scale beyond any requested start where
   `side_j*(1-w_j)>C`, for EVERY rational C on the actual afNomeSchedule.
   Hence `side_j*(1-w_j^12)>C`. The literal signed spatial family has
   bare-product-heat eigenvalue w^12 (`FamilyHeatEigen.spatialSpan_fullRange`).
   Time box smoothing cannot change the normalized energy of a pure mode.
   This rules out a bare-heat replacement as a family-uniform H1 producer;
   it is NOT an eigenvalue statement for the actual interacting K(V·).
2. For SAME original ell_V moments C=<c,c>, Q=<c,Tc>, B=<Tc,Tc>,
   R=<Tc,T²c>, y=C*Tc-Q*c, prove
   `<y,Ty>=C*(C*R-Q*B)-Q*(C*B-Q²)` and
   `<y,y>=C*(C*B-Q²)`. Actual transfer positivity then gives
   `C*(C*R-Q*B)>=Q*(C*B-Q²)` without C>0 or division.
   This locates the temporal Gram determinant needed for useful filtering
   spread; it does not supply a family-uniform lower bound on that determinant.

Available inputs: the rational AF denominator and Nat geometric-growth proof
already in AFPaddedTrajectory, actual weighted transfer symmetry/linearity,
support and positivity already in SourceRayleighPersistence. Reuse those.

## Decisive tests and budget

Keep actual V and the original center/partitions in the spread identity.
The bare eigenmode has zero temporal Gram determinant: no proof may infer
strict spread from positivity or face cardinality. Empty/zero sources must
remain permitted; no source-norm inverse, new axiom/hole, canonical field
weakening or stronger assumed survival input.

Only changed leaves will be checked, serialized through the safe launcher:
one 20-GiB worker, 12-GiB OS reserve, fresh capacity preflight per launch.
No full build/audit, bare compiler, heartbeat/recursion-limit increase or
routine literature scan. Sol handles independent bounded proof work; root
alone compiles. Abandon an intended consumer if it substitutes bare heat for
the actual transfer or claims that a nonnegative determinant is a useful
uniform positive spread bound.

## Observed result

Both selected leaves pass focused verification.

### Constructed cofinal bare-heat screen

In `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean`:

- line 359, `afBareHeatProbeScale`, returns an explicit natural probe from
  the supplied rational cap and starting index.
- line 362, `afBareHeatProbeScale_ge_start`, proves the probe is beyond that
  start; line 374, `afGap_side_gt_at_probe`, proves side times coupling loss
  exceeds that cap.
- line 419, `afGap_le_bareHeatLoss`, retains the actual w^12 family-mode loss.
- line 434, `afBareHeatLoss_side_gt_at_probe`, and line 448,
  `afBareHeatLoss_no_uniform_cap`, exclude even an eventual rational cap on
  `side_j*(1-w_j^12)` for this schedule.

This is a kernel-checked scalar scaling obstruction, not an interacting
eigenvalue theorem. The bare-family eigenpin is independently
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyHeatEigen.lean:42`,
`spatialSpan_fullRange`. The discussion of pure-mode smoothing and the area
constant is a mathematical route screen, not an additional Lean theorem
about the interacting completed family. No actual Wilson H1 is refuted.

### Original temporal spread estimate

In `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceRayleighPersistence.lean`:

- line 308, `sourceRayleigh_spread_residual_supported`, keeps y on the
  original polynomial carrier.
- line 322, `sourceRayleigh_spread_transfer_identity`, proves the exact
  transfer quadratic; line 371, `sourceRayleigh_spread_square_identity`,
  identifies the source CS gap with the residual square multiplied by C.
- line 408, `sourceRayleigh_spread_step`, proves
  `Q*(C*B-Q²)<=C*(C*R-Q*B)` from the actual transfer quadratic positivity.
  No source norm is inverted; zero sources remain covered. There is no
  assumed source-relative floor, positive-norm guard or spectral theorem.

These moments use the original finite V-weighted pairing. They are not
identified with a reflected completed norm. A useful quantitative lower
bound on the temporal spread for the actual selected AF family remains
unsupplied, as does the completed/covariance join needed to consume it there.
The standalone spread theorem assumes w>=0 and support; normalized Rayleigh,
nonnegative-norm and CS-gap interpretations additionally require the actual
positive spatial-weight and, where used, positive-norm guards. Neither a
positive determinant nor Rayleigh monotonicity forces proximity to the SAME
vacuum rate: modes can all remain fast. No such inference is made.

### Verification boundary

Final logs and SHA-256:

- `/private/tmp/ym-oct7-af-bare-cofinal2.log`:
  `2bee467bf419b53d0462b5199dfa6e00b7bcaf2ade1be90dd8e5da8dcc93a388`.
- `/private/tmp/ym-oct7-source-temporal-spread1.log`:
  `9da92f4fd3eab5df5c35f01a02a60e635cd47de791f5e42a621269d837136c67`.

All new printed gates are inside {propext, Quot.sound}; the probe definition
is axiom-free. The first screen check hit elaborator recursion depth at a
large definitional cast. An explicit projection rewrite repaired it; no
recursion/heartbeat limit was raised. Failed elaboration is not evidence.
The spread-square proof reports an unused support argument, not a proof hole.
Fresh preflights found 87--88 percent system-wide free memory, zero swap and
no competing compiler. Checks were serialized with one 20-GiB worker and a
12-GiB reserve. No full-root/tree build/audit or hashed-baseline refresh.
No new source sorry, axiom, classical input or canonical field change.

## Decision and next mathematical estimate

PRUNE the bare-heat replacement as a uniform selected-family H1 producer.
CONTINUE the original interacting response calculation, retaining the entire
OWN-centered spatial family, its off-diagonal correlations and partitions.
The source/action contribution is explicit in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepSourceDerivative.lean:80`,
`lastStepSourceDerivative_expansion`: D(V) multiplies the complete paired
residual and cannot be removed by the bare Casimir identity.

Next seek an actual interaction-sensitive response-area estimate, or a
quantitative temporal-spread estimate sufficient for the existing shifted H1,
including the actual vacuum-rate normalization and completed-moment join.
Do not infer such an estimate from nonnegative variance, positive initial
norm, spatial face count, or the bare eigenpin. The existing area consumer
is sufficient; no further assuming-the-area wrapper is needed.

Independent review also identifies the signed term to preserve in a source
calculation. Writing W=V*a, c=a*psi, A=K(W) and b=K(W*psi), the product rule
and the cited angular carrier identity give the inspection-level split
`A*D(b)-b*D(A) = A*K(W*D(psi)) + [A*K(D(W)*psi)-b*K(D(W))]`.
For psi=f-mu the bracket's constant-center terms cancel, but D(W) still
contains BOTH V*D(a) and a*D(V). This is an algebraic reading of the existing
source/action identity, not a new checked estimate or a new family-smallness
lemma. Estimate the mixed signed contribution before taking absolute bounds;
do not replace it by a blanket full-noise ceiling.

The user's lattice-mass note is already incorporated, with primary-source
corrections, in `audits/RESEARCH-LATTICE-MASS-CALIBRATION-2026-10-07.md`.
Independent rereview found no missing input that changes this plan. A fitted
channel mass supplies none of the missing estimates.

Actual interacting covariance shape, temporal spread/survival, all-vector
changing-action comparison/useful delta budget, physical/volume control,
limiting QFT and every group remain OPEN. No displayed chart claim changes.
