# Defect-retaining collective estimates: revised quantitative entry test

Date: 2026-09-30 UTC. Source baseline: `431b62d`.
This is mathematical/source review and targeted primary-paper research,
not a new Lean theorem or an analytic estimate. No Lean file was changed
and no compiler, SDP, large enumeration or routine math-ph scan was run.

Follow-up: `audits/AUDIT-ENERGY-RELATIVE-RESIDUAL-2026-09-30.md`
records the subsequently checked local residual-energy approximation
upgrade. It resolves that specific local-error issue below, not the signed
collective estimate, omitted-mode control, or a same-operator finite-size
criterion. The original source-baseline findings here remain historical.

## Decision

Keep the original signed estimate primary, but do not impose pairwise
absolute bounds or the previously proposed 18/L-3/L^2 patch threshold as
necessary conditions. Retain positive prediction defects when searching
for a collective certificate. Refined inverse-square finite-size criteria
are a separate possible route, not yet transferred to this carrier.
Their published constants also need a feasibility check; an asymptotically
better exponent alone does not justify a numerical launch.

## What the existing original-action identities actually require

On the same completed full-action carrier, write P_i for its singleton
conditional projections, R_i=I-P_i, H=sum_i R_i and E(y)=<Hy,y>.
For each ORDERED distinct neighboring pair, write

```
C_ij(y) = <P_i y,P_j y> - ||P_{[i,j]} y||^2,
D_ij(y) = ||y-P_i y-P_j y+P_{[i,j]} y||^2.
```

These are existing objects, not new freely supplied functions:

- `predictionCovariance` and `predictionDefect`,
  `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:148`
  and `:153`;
- `residual_pair_decomposition` in that file at `:168`;
- `conditionalProjection_singleton`,
  `lean/YMGap/Continuum/BF4ExactSlabBlockSingletonProjection.lean:159`,
  identifies those singleton block operators with the sweep's actual stars;
- `conditionalGenerator_square` and `remoteEnergy_nonnegative`,
  `lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`
  and `:79`.

Composing these identities on paper gives

```
||Hy||^2 = E(y) + sum_adj (D_ij(y)-C_ij(y)) + remoteEnergy(y).
```

Consequently a sufficient missing estimate is

```
sum_adj C_ij(y) <= sum_adj D_ij(y) + (1-gamma)*E(y),   gamma>0.  (*)
```

Keeping remoteEnergy on the right would weaken this requirement further.
There is no factor-of-two adjustment in (*): both sums use ORDERED pairs.
This preserves cancellation between pairs and the nonnegative defect
squares. It is less restrictive than certifying every covariance separately.
It is NOT proved by the exact identities themselves.

For the descent route, the estimate must hold at every gradient-step
iterate starting from each needed balanced Chebyshev auxiliary, not just
at the initial auxiliary. The existing theorems quantify over all states:
`energy_contract` and `step_telescope`,
`lean/YMGap/Continuum/GNSResidualGeneratorDescent.lean:112` and `:175`.
An orbit-restricted proof would have to instantiate their pointwise algebra
at every step; no such refinement or new assumption bundle was added.

The current feature-wedge identity does not solve (*).
`covarianceVector_wedge_pin` and `wedgeBudget`,
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFeatureWedge.lean:89` and `:98`,
rewrite a pair numerator, not the collective defect-corrected form.
The existing certificate consumer `residual_pair_lower_of_certificates`,
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:83`,
still requires the displayed pairwise budget. No useful collective
coefficient has been computed or proved by this review.

## Primary-source alternatives and their limits

**Anshu**, [arXiv:1909.01516, Theorem C.1](https://arxiv.org/pdf/1909.01516),
gives, under its stated size and gap hypotheses, a local/global comparison
with threshold `200*layers^2*g^2*6^D/(min side)^2`. It uses the minimum
subsystem gap, not its average. Its finite-dimensional spin setting is not
automatically the weighted completion here. No theorem was imported.
Here layers counts commuting layers and g counts noncommuting terms;
the repo's color/neighbor counts alone do not establish the theorem's setup.

Arithmetic screen ONLY: if a valid transfer eventually allowed D=4,
layers=8 and g=25, the displayed constant would be 10,368,000,000.
Its threshold beats the earlier proposed `18/L-3/L^2` only when
`L>(10,368,000,003)/18`, first integer L=576,000,001. Thus copying those
constants would not yield a modest-size numerical pilot. This compares
threshold formulas, not two established bounds on our operator. A tiny
exact `Fraction` calculation verified the arithmetic; no Lean proof was run.

**Lemm--Lucia**, [arXiv:2409.09685v2, Lemma 2.4 and Proposition 2.5](https://arxiv.org/html/2409.09685v2#S2),
relate subsystem projector overlap to
`C1*exp(-C2*sqrt(lambda_k)*ell_k/s_k)` and combine summable overlaps in
a multiscale gap product. Their result covers general finite-range spin
interactions on the specified embedded graphs. It still needs sufficiently
slowly closing subsystem gaps; positivity at each finite size is insufficient.

Repository comparison: actual block towers and nonneighbor commutation
exist (`tower`, `reverse_tower`,
`lean/YMGap/Continuum/BF4ExactSlabBlockTower.lean:89`, `:101`;
`conditionalProjection_commute`,
`lean/YMGap/Continuum/BF4ExactSlabBlockNonneighborCommutation.lean:142`).
They do not identify arbitrary subsystem ground spaces or supply quantitative
overlap decay. The checked scalar Chebyshev calibration is not that operator
overlap theorem. A same-carrier constructive proof and boundary accounting
would still be needed; ordinary conditional dynamics is not physical OS time.

**Rai et al.**, [arXiv:2411.03680v3, Section 2 and Appendix D](https://arxiv.org/html/2411.03680v3),
search for local positive decompositions of `H^2-gamma*H`, allowing
telescoping corrections. Appendix D warns that local numerical slack
`-epsilon*I` accumulates with system size. Their certified variant preserves
the local ground kernel before correcting the candidate gap. The presented
SDP is finite-dimensional and translation-invariant; its Glauber example
is one-dimensional, not this SU(2) theory.

For this repository, a prospective Rust/SDP producer must supply an exact
rational certificate or a proved error relative to the SAME energy budget,
including omitted modes and boundary terms. A principal finite matrix alone
does not cover the infinite local polynomial degree. Existing
`residual_relative_bracket`,
`lean/YMGap/Continuum/BF4ExactSlabStarVariationalApproximation.lean:156`,
has error epsilon times the original STATE NORM, not epsilon times E(y).
Do not silently turn it into an energy-relative error bound. This is a
specific missing estimate, not permission to make the finite test an oracle.

## Scope checks and execution consequence

The original finite and local coefficients can be strictly positive without
being useful on scaling. In particular the current degree-dependent local
factor is already proved to approach one by `factor_approaches_one`,
`lean/YMGap/Continuum/BF4ExactSlabLocalChebyshevObstruction.lean:203`.
That branch must not be restarted by rephrasing its coefficient.

Likewise, no cone-saturation obstruction was found in the targeted
`BF4ExactSlabEightLayerCone`, `ConeSize`, `ConeCoordinateDistance`,
`ChebyshevCovariance` and `ChebyshevFiniteCovariance` modules. Increasing
the cone can restrict available separation, but this review does NOT prove
that every degree has no separated probes. The degree-one exact factor is
strict whenever its explicitly stated hypotheses hold.

NEXT: seek a quantitative original-action proof of (*) with its actual
state/orbit scope, or a subsystem/overlap estimate with an explicit viable
finite-size budget. Do not launch a dense expansion or SDP until its finite
size, omitted-mode error and original-law pin are controlled. Do not require
uniform global coercivity as the only conceivable intermediate input, and
do not implement another conditional compiler without a prospective producer.

Sol reviewed the defect identity, ordered-pair bookkeeping, descent scope,
primary-paper formulas and threshold arithmetic; Luna reviewed coefficient/
separation scope. The raw Q' constructor
stores denominator minus one: `geometricCalibration=⟨2,624⟩` is 2/625,
as confirmed by `geometricCalibration_cancel` in
`lean/YMGap/Continuum/BF4ExactSlabFiniteVolumeReverseEnergy.lean:43`.

A03 and the full same-theory continuum/QFT/physical mass/every-group Clay
target remain open. No canonical chart state changed.
