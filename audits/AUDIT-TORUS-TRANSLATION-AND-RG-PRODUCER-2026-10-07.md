# Checked torus joins and RG producer correction (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple gauge group, the required SAME-theory
QFT structure, and a positive physical Hamiltonian mass gap.

The previous checkpoint was `4a0581cf`. This continuation joins finite algebra
and removes an unnecessary comparison requirement; it supplies neither of the
two missing AF analytic producers (survival and all-vector gap control).

## Actual finite torus translation and covariance

The link permutation is not assumed. The literal periodic time shift has an
explicit inverse on physical links; the inverse-list index agrees exactly with
the original forward-shifted index:

- `lean/YMGap/Continuum/SU2TorusLinksTimeShift.lean:59`,
  `torusLinks_timeShift_perm`.
- `lean/YMGap/Continuum/SU2TorusLinksTimeShift.lean:89`,
  `inverseShift_idxOf`.
- `lean/YMGap/Continuum/SU2TorusLinksTimeShift.lean:111`,
  `torusPlaquettes_timeShift_perm` (the complete list, temporal factors included).

Supported Haar relabelling identifies the actual plaquette word and full Wilson
weight, giving the unnormalized moment and OWN mean identities:

- `lean/YMGap/Continuum/SU2TorusOwnMeanTimeShift.lean:96`, `inverseShift_word`.
- `lean/YMGap/Continuum/SU2TorusOwnMeanTimeShift.lean:120`, `inverseShift_weight`.
- `lean/YMGap/Continuum/SU2TorusOwnMeanTimeShift.lean:136`,
  `character_moment_timeShift`.
- `lean/YMGap/Continuum/SU2TorusOwnMeanTimeShift.lean:156`, `ownMean_timeShift`.

Both means use the literal SAME partition reciprocal. No cancellation or
positivity premise is needed for their equality. `perm_haarX`'s legacy
propositional witness is used only inside a propositional integral identity,
never extracted as data for a computed object.

For `p=((1,b,c,d),plane)`, the constructed family is the OWN-centered character
at each translated root, and its response is literally `rpB(tau0,taun)`:

- `lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:43`, `tau`.
- `lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:48`, `response`.
- `lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:64`,
  `response_covariance`: `response n ≈ Z*SU2ClusterBridge.cov n`.
- `lean/YMGap/Continuum/SU2TorusCenteredCovarianceRP.lean:113`, `hcov`, supplies
  that exact input over the existing bridge's finite range.

All roots are present and distinct: `b,c,d<2M`, a spatial plane and `n+1<=M`;
the range theorem uses `2X+1<=M`. Reflection, OWN centering and SAME positive
partition cancellation are the already checked ingredients. This narrow `hcov`
join itself does not need translated-mean equality, since each root is centered
at its OWN mean. The translated-mean theorem is needed for the fixed-source
translation and pairing assembly.

This is finite Taylor-Wilson data at the existing fixed `betaS` and cutoff K.
It is not automatically the original all-nome heat-action completion below.
Positive-half `PtSup`, the weighted pairing shift law, a torus transfer, and
changing-scale/volume control remain OPEN.

## A genuine obstruction, with its unnecessary premise removed

The actual original completed carrier has a nonzero boundary-plaquette norm
whose positive-time image is zero. Therefore a map factoring through positive
time, followed by zero-preserving postprocessing, cannot meet a coercive lower
comparison on the FULL vacuum complement:

- `lean/YMGap/Continuum/BF4WilsonAllNomeRGTimeSmoothingObstruction.lean:80`,
  `no_coercive_positive_time_smoothing`.
- `lean/YMGap/Continuum/BF4WilsonAllNomeRGTimeSmoothingObstruction.lean:102`,
  `approxRg_not_positive_time_smoothing`, applied to the existing full interface.

But coercivity is NOT used by the actual gap transfer. The smaller sufficient
comparison, now proved separately, is

```
||Phi x||_c^2 <= ||x||_f^2
||Tf^2 x||_f^2 <= kappa*||Tc Phi x||_c^2
                  + kappa*epsilon*||x||_f^2.
```

Given the coarse vacuum-square contraction at rate rC and `kappa>=0`, this
implies the fine two-step factor `kappa*(rC^2+epsilon)`:
`lean/YMGap/Continuum/BF4WilsonAllNomeRGTimeSmoothingObstruction.lean:51`,
`twoStepFactor_of_upper_comparison`. No coercive lower comparison, linearity,
zero-preservation or norm division is required.

The SAME computed-rate induction consumes these smaller actual comparisons:
`lean/YMGap/Continuum/BF4WilsonAllNomeRGComputedMargin.lean:308`,
`computedRate_contraction_of_upperComparisons`. It still needs ONE seed,
`kappa>=1`, `epsilon>=0`, a useful weighted effective-defect budget and positive
`seedFloor=seed*(1-seed)-S/2`. It derives the factor caps and all-scale
contractions instead of assuming them. Those contraction proofs fit the existing
`exprWilsonFamily` constructor alongside the already proved numeric rate bounds;
the dyadic floor is `computedMargin_lower` in the same module.

The old `ApproxRgIntertwiner`, its lower-bound field, old rate-chain fields and
canonical Clay targets are unchanged. The smoothing obstruction prunes only
attempts to inhabit the FULL interface. It does not prune the smaller gap
producer, nor construct such a producer.

## Next action-specific estimate

The original action gluing is explicit:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTwoLayerGluing.lean:61`,
`middleIntegrand`, retains `K01*V1*K12`; `gluedMiddle` at line 73 integrates that
COMPLETE middle factor. `original_twoLayer_gluing` at line 201 pins the SAME
original endpoint observables and action. Bare heat semigroup composition
does not remove the written `V1` factor.

Next: produce the upper/two-step comparison on the original completed form,
keeping that full action, or prove a direct SAME-operator bound. The demanding
weighted distortion/error budget and independent AF window survival remain
unproved. An ordinary weighted L2 averaging estimate cannot be substituted for
this OS/completed-form comparison without its own proved identification.

## Verification boundary

Five final focused checks passed, with every printed gate inside
`{propext, Quot.sound}`. Successful local logs:

- `/private/tmp/ym-oct7-links-timeshift.log` (8 sites).
- `/private/tmp/ym-oct7-own-mean-timeshift.log` (5 sites).
- `/private/tmp/ym-oct7-centered-covariance-rp.log` (2 sites).
- `/private/tmp/ym-oct7-rg-time-smoothing-obstruction.log` (3 sites).
- `/private/tmp/ym-oct7-computed-margin-minimal.log` (14 sites).

Checks were serialized through `scripts/safe_lean_build.py`, one worker,
20-GiB ceiling, 12-GiB reserve, with dynamic process/pressure/swap preflight.
No swap growth occurred. One target was stopped immediately on seeing the
launcher's obsolete default ceiling, then relaunched with explicit 20 GiB;
that interrupted launch is not verification evidence. Missing dependency
caches were resolved with narrow dependency-complete targets. Failed source
elaborations are not evidence; final checks pass without raised heartbeats,
source holes or new axioms. No root/full-tree build, audit or guard was run;
CI remains off. The canonical broad chart is unchanged, so it is not reprinted.
