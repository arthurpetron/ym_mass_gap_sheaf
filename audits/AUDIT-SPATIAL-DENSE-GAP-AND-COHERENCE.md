# Spatial-limit form, base coherence and strict dense two-step bound

Date: 2026-09-16. Baseline: `eda63b9`.

The whole-project goal remains a constructive nontrivial continuum
Yang--Mills theory on R^4 satisfying the required QFT axioms and having a
positive physical Hamiltonian gap, for every compact simple group. This
checkpoint does not close that goal. Its actual objects are the original
SU(2) reflected signed plaquette-character presentations at fixed lattice
spacing, under explicit small-nome assumptions.

## Proved causal chain

Paths are relative to the repository root. Declaration namespaces match
their module names. The table records actual producers and consumers,
not merely proposed diagram arrows.

| Declaration | Source | Proved consequence / consumer |
| --- | --- | --- |
| `spatialPairing`, `spatialPairing_converges` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingLaws.lean:59`, `:70` | Original recentered joint forms converge to this same spatial reflected form. |
| `spatialPairing_cauchySchwarz`, `spatialPairing_radical_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPairingLaws.lean:106`, `:139` | Limiting CS proves radical descent; no inference from limit-nullity to finite-width nullity. Symmetry, positivity, unit normalization and rational bilinearity are also supplied. |
| `spatialPairing_null_congr`, `spatialSeminorm` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialSeminorm.lean:111`, `:138` | Actual squared-distance laws supply the existing explicit-Cauchy quotient machinery. |
| `SpatialCompletion`, `spatialCompletedTime`, `spatialTime_cauchy_modulus` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPhysicalTime.lean:122`, `:127`, `:151` | Physical time acts on this new quotient, retaining each supplied Cauchy modulus. Zero/addition/embedding laws are proved. |
| `spatialCompletedUnit_fixed`, `spatialCompletedUnit_ne_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialPhysicalTime.lean:157`, `:189` | The actual normalized unit is fixed and nonzero; uniqueness of the vacuum is not claimed. |
| `inclusion`, `inclusion_time` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseInclusion.lean:45`, `:66` | Include unchanged face words into a larger base; commute with actual physical time. |
| `omitted_separation`, `aligned_chartInsertion_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseAlignedBoxes.lean:174`, `:275` | Exact time alignment of selected actions and original reflected insertions, with spatial separation of omitted faces. |
| `chartScalar_inclusion_bound`, `inclusionModulus`, `spatialPairing_inclusion` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:217`, `:243`, `:294` | Explicit original-action comparison proves equality up to CReal equivalence after spatial exhaustion for unchanged words in enlarged bases. |
| `finite_covariance_distance_bound` | `lean/YMGap/Continuum/BF4ExactSlabSelectedTwoProbeCovariance.lean:86` | The selected-action connected numerator estimate yields normalized covariance decay, cancelling the same positive partition square. No full-slab state is substituted. |
| `probeBoxSize`, `chartProbe_separated`, `upperProbe_local`, `lowerProbe_local` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSeparatedProbeControl.lean:63`, `:75`, `:126`, `:134` | Two separate fixed-size boxes support the literal probes; their size does not grow with the temporal gap. Interval certificates are at `:95`, `:110`. |
| `connectedScalar_selected_pin`, `connectedScalar_uniform_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:135`, `:193` | The actual chart joint moment and both marginals use the same selected action and partition. Their covariance has a regulator- and lag-independent amplitude. |
| `originalConnected_diagonal_converges`, `spatialEvenMoment_dyadic` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:127`, `:101` | The original connected diagonal converges to the same centered spatial form; its even moments retain sharp dyadic CS independently of any decay estimate. |
| `shifted_bound` | `lean/YMGap/Continuum/RationalShiftedGeometric.lean:55` | Explicitly absorbs the truncated support-size loss into a positive prefactor for every lag, including the initial segment. |
| `spatialEvenMoment_first_le`, `dense_vacuumComplement_twoStep_bound` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:133`, `:158` | Dyadic prefactor removal gives a common strict two-step form rate on every dense presentation orthogonal to the actual unit. |
| `spatialCenteredFace_floor` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:170` | The same centered spatial scalar retains the original positive local character-variance floor. This is not yet a centered completed vector. |

## Explicit constants and uniformities

Fix `0<w<1`, `base>0`, presentations `x,y : PhysicalSpan base`, and
`R >= radius(x), radius(y)`. The analytic guards remain

```text
heatRatio(w) <= 1/2
delta(w) = heatRemainderBound(w) < 1
rho(w) = 625 * adjustedCoreRate(w) < 1.
```

No new analytic input is assumed. Definitions are
`heatRemainderBound` and `heatRemainderBound_eq` at
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:82`, `:85`,
`pairedHeatRate` at
`lean/YMGap/Continuum/BF4ExactSlabConnectedCoefficientBound.lean:45`,
`inverseFaceFloor`, `probePrefactor`, `adjustedCoreRate` at
`lean/YMGap/Continuum/BF4ExactSlabCollarAdjustedRate.lean:41`, `:44`, `:47`,
and `entropyRate` at `lean/YMGap/Continuum/FiniteSizeGeometricSum.lean:58`.
In rational-setoid notation these give

```text
delta = 128*w^3
f     = 1/(1-delta)
rho   = 625*(delta+delta+delta^2)*f^48
N     = max(base,R+1)
M     = 12*N^4
L     = 24*N^4
c     = spanCap(x), d = spanCap(y)
A     = (c*d+c*d) * f^(12*(L+L)) * (2^M*625^M)/(1-rho)
P     = A/rho^M + 1 > 0.
```

The actual definitions `sizeLoss`, `probeLinkCount`, `decayAmplitude` are
at `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformConnectedDecay.lean:66`,
`:71`, `:76`. `positivePrefactor` is at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:102`.
Their denominators are supplied by explicit strict-positivity proofs.

For every margin `r`, heat stage `k`, boundary-time buffer `t`, and physical
lag `n`, the original connected chart scalar satisfies

```text
|C(r,k,t;n,x,y)| <= A*rho^(R+n+1-M) <= P*rho^n.
```

Subtraction in the first exponent is natural truncated subtraction.
`A` and `P` depend on coupling, base, observation radius and original signed
coefficient/representation lists, but not on `r,k,t,n`. `rho` depends on
coupling, not on base, support, lag or any regulator. The two boxes of
side `N` are translated separately: their connecting gap is not included
in their size. This is the step that prevents a lag-dependent prefactor.

For each fixed lag, genuine product continuity passes all three original
moments to their common spatial limit. Set

```text
M_n(x,y) = B(x,T_n y) - B(x,1)*B(1,y)
a_k      = M_(2*k)(x,x).
```

`spatialCenteredMoment` and `spatialEvenMoment` are defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialCenteredForm.lean:53`,
`:83`. They satisfy `0<=a_k<=a_0`, `a_k^2<=a_(2*k)*a_0` and
`a_k<=P*(rho^2)^k`. The existing constructive dyadic argument therefore
gives `a_1<=rho^2*a_0` without dividing by `a_0` or assuming it positive.
For `B(x,1)=0`, this is exactly

```text
B(x,T_2 x) <= rho(w)^2 * B(x,x),    0 < rho(w)^2 < 1.
```

Positivity and strictness of the common two-step rate are checked by
`twoStepRate_positive`, `twoStepRate_lt_one` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSpatialDenseGap.lean:68`, `:72`.
This is the reflected physical-time map on these presentations, not a
Markov/heat-bath generator. No continuum Hamiltonian is constructed here.
The statement is neither beta-uniform nor unrestricted-nome; no physical
lattice-spacing parameter or continuum mass calibration is supplied.

## Base coherence and nontriviality: exact scope

For `base<=larger`, unchanged words are included in the larger base.
The action comparison aligns their chart times by `larger-base`, with
ambient extent increased by twice that amount. Both orientation-dependent
time endpoints are retained. `inside_finiteValue_pin` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBaseCoherence.lean:98` pins the
filtered target action to the original source action, including its
partition. The boundary error tends to zero with the explicit
`inclusionModulus` at `:243`; `spatialPairing_inclusion` at `:294` gives
the limiting equivalence.

This is not equality of finite-width states, invariance under arbitrary
spatial translations, a constructed union carrier, or an identification
of completed carriers. The separate spatial-limit Cauchy quotients now
exist, but their completed mixed inner products have not been supplied
in this checkpoint.

The actual spatial centered character scalar is at least `starRatio(w)`;
`starRatio_positive` at
`lean/YMGap/Continuum/BF4ExactSlabLocalStarComparison.lean:65` proves this
floor positive. It is a scalar nontriviality witness, not yet an actual
nonzero centered vector in the new spatial completion. The already
constructed nonzero unit is not a substitute for that excitation.

## Remaining causal frontier

The next consumer is the SAME spatial Cauchy carrier's completed mixed
pairing and centered sector. Construct rational approximations to the
actual character mean, prove their explicit Cauchy modulus and completed
orthogonality, and pass the centered scalar bound to every completed
unit-orthogonal vector. These are open steps, not additional hypotheses
introduced into the dense theorem.

Base coherence enables a presentation-independent union construction but
does not perform it. The full spatial-translation and observable-algebra
identifications, Hilbert/OS/QFT reconstruction, physical time/spacing
calibration, controlled continuum passage and nontriviality, and every
compact simple gauge group remain open. No canonical frontier field or
scorecard closure is claimed by this checkpoint.

## Verification boundary

Twelve narrow serialized checks passed through `scripts/safe_lean_build.py`,
with one worker and a 20 GiB worker ceiling. All 139 printed public axiom
gates were within `{propext, Quot.sound}`. Final logs contain no errors,
warnings, `sorryAx`, classical dependency or native reduction axiom.
Initial namespace/API errors were corrected before the final successful
checks; failed checks were not treated as proof evidence.

Independent read-only source review checked the same actions and partitions,
actual support placement, regulator/lag quantifiers, limiting radical
descent, prefactor removal and dense/completed boundary. No new sorry,
axiom, classical shortcut, analytic premise, weakened canonical field or
safety-limit change was introduced.

Final local log evidence (hashes are of logs, not source files):

| Log under `/tmp/` | Gates | SHA-256 |
| --- | ---: | --- |
| `ym-spatial-form-laws-20260916.log` | 19 | `a160786f2852695d426552dea13c204d4d6cf11af63205d0b55dd0c37cbdd924` |
| `ym-spatial-seminorm-20260916.log` | 11 | `150ec0107fcdeca305e4fb2577e4a6f30a6347359a803cf2b916f93e1a619e5c` |
| `ym-spatial-time-20260916.log` | 20 | `a7ebc68085a87660bfea83bb43d54c4d215ea8dc6b94c697cd2ef5d51e90b0fc` |
| `ym-base-inclusion-20260916.log` | 15 | `c0c4b3745939eb708aed023734c823eccf4bd0ef6419d5b1669861382d8c6945` |
| `ym-base-aligned-20260916.log` | 20 | `ebd2339ac32baa246934b100612e65a7743ab4ad5fff0e57fdb4dc930f7a58a6` |
| `ym-base-coherence-20260916.log` | 7 | `c5c6ea4e6fe4fe65d025fdc93fa85eccf022bc0d67b2bb3b62353d76caad1749` |
| `ym-selected-two-probe-20260916.log` | 4 | `8070b4d52bd817d8337d597f5d24599f087bea496f0a41b14bd6790384cf5813` |
| `ym-separated-probe-control-20260916.log` | 11 | `741349b405b2037b4b1d456883d7f9a6cb2dc9da7379aa41e4aa8d1b22d9dc95` |
| `ym-uniform-connected-decay-20260916.log` | 6 | `f1fd18d35a3c87046c7a466e834d664373931b4284adaaa38ecfd8ab9f596c86` |
| `ym-spatial-centered-20260916.log` | 8 | `1d6a1f4a3b9154bee40e4669e2b816961d3fe034f9ece08fc9483e8356bf3456` |
| `ym-shifted-geometric-20260916.log` | 5 | `cdd00f78a0c7a22932a1582a296d7b5ab30dfe20449fb1a350fc18309cbadd84` |
| `ym-spatial-dense-gap-20260916.log` | 13 | `1e12bfeb7a3f2c5dec17275a90baeb38b968084bc359a76f8a8ab2a8d0145c82` |

Twelve imports were added to the selective root. No root build, full-tree
build or full audit ran. No routine literature scan ran; the cached
math-ph review and minimum 12-hour interval remain in force.
