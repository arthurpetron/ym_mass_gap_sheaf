# Original finite-family Rayleigh floor and reference-certificate screen

Date: 2026-10-04 UTC. Three public declarations checked; no continuum closure.

## Mathematical result and scope

For the literal signed fundamental-plaquette family
`F = sum_{p in qs} coeff(p) * chi(p)`, let `N = qs.length`,
`S = sum coeff(p)^2`, `V = oddVariance(F)` and `E = normalizedEnergy(F)`.
The action, terminal messages, partition and OWN center are unchanged.

1. `V <= 4*N*S`, including repeated and empty lists. This uses the exact
   SU(2) character square cap, finite Cauchy under the original positive odd
   marginal, and subtraction of the SAME mean square. Declaration:
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRayleighFloor.lean:104`,
   `family_oddVariance_coefficient_cap`.
2. For distinct physical faces, `lower(w)*V <= 2400*upper(w)*N*E`.
   The coefficient-square sum cancels by composing the cap with the existing
   `lower(w)*S <= 600*upper(w)*E`. New declaration:
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRayleighFloor.lean:187`,
   `family_energy_variance_floor`. Existing input:
   `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteFamilyEnergy.lean:174`,
   `family_energy_floor`.
3. An accepted EXISTING finite-reference certificate on the literal padded
   family necessarily satisfies `lower(w) <= 2400*upper(w)*N*c`.
   Declaration:
   `lean/YMGap/Continuum/BF4WilsonAllNomeFamilyReferenceScreen.lean:55`,
   `certificate_coefficient_necessary`. The positive accepted margin and
   nonnegative actual energy imply `V>0`; only then is `V` canceled.

The first two results hold at every width and terminal depth, at every cutoff
`K >= headCutoff(w)`, for each strict nome `0<w<1`. The lower coefficient is
positive at fixed nome and bounded nonzero family length. It explicitly
depends on nome and list length; it is NOT coupling- or spacing-uniform.
The screen also retains strict base-to-width padding and physical membership.

## Forward/backward connection

Forward: the cap is integrated under the actual `marginalCertificate`, not
an auxiliary free law; `marginalVariance_pin` returns the actual OWN variance.
These declarations are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:89`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:93`.

Backward: the existing checker requires a positive ORIGINAL energy/variance
margin, not a new hypothesis bundle. Its acceptance and strict-ratio consumer
are `check` and `Certificate.reference_strict_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:267` and
`:308`. The exact family pins are `finite_family_energy_pin` and
`finite_family_variance_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyBondFloor.lean:147`
and `:155`. They preserve the same cutoff, depth, source, action and center.
Thus the screen rejects an infeasible proposed `c` without expanding moments.

If a candidate seeks `c -> 0` along this unfiltered family-reference route,
fixed nome and uniformly bounded family length are incompatible with these
inequalities. Width changes or signed coefficient renormalization alone do
not fix that. This conditional statement does NOT assert that every survival
route requires such an unfiltered coefficient. The filtered-window consumer
`original_window_budget_macro_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245` instead
requires the aggregate signed cost versus the SAME filtered-start variance.
It remains open and is not ruled out by this floor.

Mere certificate acceptance does NOT demand `c -> 0`:
`Certificate.completed_ratio` at
`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:332`
uses `D=c*(1+comparisonEta)^2`, defined by `referenceCoefficient` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:42`.
The generic fixed-carrier consumer `response_geometric_lower` at
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseLower.lean:117` propagates a
supplied one-step response fraction. Shrinking the loss as a horizon grows
is a sufficient geometric-guarantee route, not necessary for true filtered
macro retention. The dyadic preimage's `m*defect <= C*response` requirement
is `halfAnchorPreimage_norm_cleared` at
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:204`;
that theorem is for the literal square excitation, not an arbitrary family.
No family-certificate-to-physical-trajectory bridge is claimed here.

## Verification

Two serialized focused checks succeeded via `scripts/safe_lean_build.py`:
jobs=1, worker limit=20 GiB, OS reserve=12 GiB, existing session lock and
continuous safety telemetry. Fresh preflights found no competing worker,
77--78% reported memory headroom and zero swap. No limit was raised.
Successful local logs:

- `/private/tmp/ym-original-family-rayleigh-floor-20261004-3.log`, SHA256
  `e5477ab4a1b55a2f4c472df9445052e74969e13650d10ec122da02a6487024e1`.
- `/private/tmp/ym-original-family-reference-screen-20261004-3.log`, SHA256
  `45e30057929ec1e127ae45f60c6077e3238162cee250fde86b574b4539fa3a92`.

All three printed gates contain ONLY `{propext, Quot.sound}`. The earlier
failed logs are diagnostics, not proof evidence. Frozen independent
mathematical/same-object review passed. Checked source hashes:

- RayleighFloor: `4b0ef2478bcab6925276f4b7560a9a40a727c78111d3f67bb22c2733632c315a`.
- ReferenceScreen: `4e57ebd7cda8f34b1610e15d7c50c4f257d7b2b12fb57b7e09724fd9c8c21899`.

Root imports are registration only; no root/full build, broad audit, guard or
metrics run. No sorry, axiom, analytic premise, resource or CI change.
No claim about an invariant plaquette-family sector or all-state gap is made.
Changing-family estimates, filtered-norm survival, physical mass calibration,
same-theory OS/full QFT, continuum construction and every-group Clay closure
remain OPEN. Supporting A03 mathematics only; exact chart claims unchanged.
