# Actual torus finite ratio and original-action producer review (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple gauge group, the required SAME-theory
QFT structure and a positive physical Hamiltonian mass gap.

Continuation of checkpoint `cf94b3de`. The finite torus source now discharges
all three algebraic inputs of the existing cluster ratio consumer. The AF
survival and changing-action all-vector gap producers remain OPEN.

## Constructed finite source, not abstract identification assumptions

All leaves use the literal `torusLinks (2*M)`, `torusPlaquettes (2*M)`,
fixed `betaS`, cutoff K and OWN means for that complete Taylor-Wilson weight.
The actual `tau` and unnormalized `response` are defined in
`lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:43`, `tau`, and
`:48`, `response`.

1. Weighted centered-pair translation is proved for any two physical roots
   and any periodic time shift, not assumed from one-point means:
   `lean/YMGap/Continuum/SU2TorusOwnMeanTimeShift.lean:192`,
   `centered_pair_moment_timeShift`. Supported Haar relabelling retains EVERY
   plaquette factor and the SAME partition reciprocal.
2. Syntactic positive-link support is proved for the actual polynomial, not
   for a Haar-equivalent substitute:
   `lean/YMGap/Continuum/SU2TorusCenteredPositiveSupport.lean:130`,
   `character_ptSup`; `:152`, `tau_ptSup`; `:176`, `hsup`.
   Actual nonzero monomial exponents lie in positive link blocks. Centering
   adds only a supported constant. Spatial time M is permitted.
3. Reflection followed by actual simultaneous translation supplies pairing
   additivity:
   `lean/YMGap/Continuum/SU2TorusCenteredPairShift.lean:64`,
   `shift_mirror_root`; `:97`, `pairing_shift`; `:124`, `hshift`.
   Thus `rpB(tau x,tau y) ≈ response(x+y)` in the written physical range.
4. The already checked covariance pin is retained:
   `lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:113`, `hcov`.
5. The direct consumer is now
   `lean/YMGap/Continuum/SU2TorusCenteredFiniteRatio.lean:33`,
   `actual_torus_ratio`. It passes the three proved inputs to
   `lean/YMGap/Continuum/SU2ClusterBridge.lean:128`, `torus_gap_bridge`.
   There are no free `hsup`, `hshift` or `hcov` premises.

With `G = response` and `E m = G(2*m)`, the exact conclusion is

```
E(k+1)^e * E(k) <= Z*(Cw*lam)*(lam*lam)^(k+e)*E(k)^e.
```

Guards: `1<=M`, `b,c,d<2*M`, spatial plane, `2*X+1<=M`, `k+e<=X`.
Every natural K is permitted, including zero. The rate is `(6/7)^2`;
the prefactor explicitly contains the actual Z. No division by source norm,
nondegeneracy, infinite-time passage or cutoff/volume limit is asserted.

## Transfer boundary stays explicit

`lean/YMGap/Continuum/SU2TransferTrace.lean:55`, `Tker`, is the actual finite
Taylor-Wilson kernel precursor; `:141`, `z_eq_trace`, identifies Z with a
periodic chain of those kernels. Its opening statement explicitly defines NO
operator on a state space. A same-carrier operator action, null-space descent,
operator laws and observable-pairing identification are not supplied by this
partition identity.

The new result is a finite-range scalar moment inequality for the fundamental
spatial character. It is not a prefactor-free strict form bound for every
vacuum-complement source. Translation of positive-half sources in a finite
torus is also not an unrestricted positive-half endomorphism. This torus branch
has not been transported to the original all-nome completed slab carrier.

## Reuse the actual existing OS scalar pin

The original interacting conditional-variance identity is already proved:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:138`,
  `blockNoise_variance_loss`.
- Same file `:177`, `filteredSquare_le_endpointSquare`.

Writing `m(p)=integral(V*p)`, `A=T^t g`, `b=T^t(g*f)`, it retains the
COMPLETE spatial action and identifies nonnegative conditional noise with
`m(g*T^(2*t)(g*f^2))-m(b^2)`. This is an upper comparison, not quantitative
survival or a strict contraction.

Its padded-square denominator is already joined to the SAME completed OS
response, not an auxiliary norm:

- `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`,
  `originalOwnBlockVariance`; `:136`, `originalOwnBlockVariance_converges`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeCenteredVector.lean:159`,
  `centeredVector_time_pairing`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:158`,
  `completedInner_time_sum`.

The limit of `m(b^2)/m(A^2)` is `Norm*Response(2*t)`, which these SAME-carrier
identities identify with the time-t squared OS norm. Nome, width, scale and t
remain fixed. Do not reopen this proved scalar pin.

Other generic pins already exist: radius-zero signed source marginal variance
reaches its ambient centered norm in
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236`,
`varianceLimit_completed_pin`; bounded multi-time original expectations have
witnessed joint limits in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:122`,
`originalJoint_diagonal_converges`, and the intrinsic form retains the same
literal-width chart in `lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:163`,
`intrinsicForm_chart`. These do not identify every multi-time source with the
particular chronological OWN-centered block variance above.

## Next actual analytic estimate

The next producer is an action-specific signed quadratic-form comparison of
the actual blocked action and the actual retained/coarse action, relative to
the surviving original OS form, uniformly over signed sources and with a
trajectory-useful weighted distortion/error budget. The already proved minimal
consumer does not require coercive lower norm comparison or preservation of
positive-norm states killed by time:
`lean/YMGap/Continuum/BF4WilsonAllNomeRGTimeSmoothingObstruction.lean:51`,
`twoStepFactor_of_upper_comparison`.

The exact original action identity to use is
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:188`,
`original_twoLayer_gluing`, with `middleIntegrand` at `:61` and `gluedMiddle`
at `:73`: the middle Haar integral retains `K01*V1*K12`. Dropping V1 changes
the written action. Neither conditional-noise positivity nor existing
fixed-parameter convergence produces the useful changing-action estimate.
Independent AF window survival, physical scaling/volume control, limiting
OS/QFT structure, every group and the Clay theorem remain OPEN.

## Verification boundary

Four final focused leaf checks passed, with all 14 printed axiom sites within
`{propext, Quot.sound}`:

- `/private/tmp/ym-oct7-centered-pair-translation.log` (6 sites).
- `/private/tmp/ym-oct7-centered-positive-support.log` (3 sites).
- `/private/tmp/ym-oct7-centered-pair-shift.log` (4 sites).
- `/private/tmp/ym-oct7-centered-finite-ratio.log` (1 site).

Narrow dependency-complete targets also passed. Checks were serialized through
the safe launcher with one 20-GiB worker and 12-GiB reserve. Dynamic capacity
was checked before each launch; swap remained zero. A failed namespace lookup
was corrected before the final passing pair-translation check. No source hole,
new axiom, raised heartbeat limit or canonical field weakening. Independent
read-only review found the SAME action, partition and guards throughout.
No root/full-tree build or audit was run; the hashed audit baseline was not
regenerated. CI stays off. Broad chart claims remain unchanged; no chart reprint.
