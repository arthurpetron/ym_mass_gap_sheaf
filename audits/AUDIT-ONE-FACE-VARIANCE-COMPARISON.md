# One-face norm-relative variance comparison

Date: 2026-09-15 (America/Los_Angeles). Base: `d00456e`.

PROGRESS: ordinary centered variance is stable, relatively and uniformly
over supported observables, under one original heat-cutoff change. This
does NOT prove spatial decay, reflected OS-norm stability, a new physical
transfer gap, or a continuum/all-group result. No canonical frontier atom
is closed.

## 1. Mathematical result and exact scope

Let B be the complete unchanged positive background, retaining all shared
links. The two actions are B*H_K and B*H_(K+L) on the same original
quaternion Haar carrier. For 0<w<1, eta>0 and
K>=relativeCutoff(w,eta), write c=1+eta. Then, for every supported p,

    E_new[p^2] <= c^2 E_old[p^2],
    E_old[p^2] <= c^2 E_new[p^2],
    Var_new(p) <= c^2 Var_old(p),
    Var_old(p) <= c^2 Var_new(p).

Each variance uses its OWN normalized mean. This does not freeze or identify
the means. In particular, Var_new(p)=0 iff Var_old(p)=0. The coefficient is
independent of the observable, extent, background, and L; the cutoff still
depends explicitly on w and eta. Only ONE heat factor changes. There is no
eta<1 guard and no supplied sup-norm cap for p.

| Declaration | Source | Role |
|---|---|---|
| `RationalPositiveRatioComparison.ratio_comparison` | `lean/YMGap/Continuum/RationalPositiveRatioComparison.lean:22` | A<=c*b and z<=c*Z imply A/Z<=c^2*b/z, retaining both positive denominators. |
| `RationalVarianceComparison.variance` | `lean/YMGap/Continuum/RationalVarianceComparison.lean:27` | b*s-(a*s)^2 from raw first/second moments and reciprocal s. |
| `RationalVarianceComparison.quadratic_decomposition` | `lean/YMGap/Continuum/RationalVarianceComparison.lean:33` | Complete the square using z*s=1. |
| `RationalVarianceComparison.quadratic_minimizer` | `lean/YMGap/Continuum/RationalVarianceComparison.lean:58` | Explicit rational mean a*s attains the minimum; no selection oracle. |
| `RationalVarianceComparison.variance_transport` | `lean/YMGap/Continuum/RationalVarianceComparison.lean:74` | Compare squared tests at the old mean, then minimize for the new law. |
| `BF4ExactSlabOneFaceVarianceComparison.mass_new_le_old` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:78` | Endpoint-relative old-mass bound. |
| `BF4ExactSlabOneFaceVarianceComparison.mass_old_le_new` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:84` | Separate new-mass bound, not division by 1-eta. |
| `BF4ExactSlabOneFaceVarianceComparison.normalizedSquare` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:89` | Literal original normalized squared moment. |
| `BF4ExactSlabOneFaceVarianceComparison.normalizedVariance` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:93` | Literal original normalized variance. |
| `BF4ExactSlabOneFaceVarianceComparison.square_comparison` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:105` | New squared moment <=c^2 old squared moment. |
| `BF4ExactSlabOneFaceVarianceComparison.square_comparison_reverse` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:117` | Reverse bound. |
| `BF4ExactSlabOneFaceVarianceComparison.variance_nonnegative` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:182` | Positivity from the actual centered square. |
| `BF4ExactSlabOneFaceVarianceComparison.variance_comparison` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:194` | New variance <=c^2 old variance. |
| `BF4ExactSlabOneFaceVarianceComparison.variance_comparison_reverse` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:211` | Reverse variance bound. |
| `BF4ExactSlabOneFaceVarianceComparison.variance_null_iff` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:230` | Same ordinary centered null observables; not OS null spaces. |
| `BF4ExactSlabOneFaceVarianceComparison.original_variance_comparison` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceVarianceComparison.lean:250` | Both estimates for the actual spectator heat product; positivity of background and both masses is constructed. |

The proof applies the original relative tail estimate under B*(p-c)^2,
not under an observable-cap estimate. Multiplying two endpoint comparisons
accounts for c^2: one factor compares square moments, the other compares
partitions. The actual spectator cutoff J is unchanged and need only satisfy
J>=headCutoff(w); it need not equal K. All positivity comes from the existing
square certificates, not pointwise positivity asserted as an axiom.

## 2. Actual consumer boundary: stop the regulator branch here

The new result is stronger than the earlier cap-dependent additive cutoff
bound: it controls arbitrarily small centered variances relatively.
Its immediate checked consequences are regulator norm and null-space
stability. A further operator consumer was NOT FOUND in the bounded review.

`BF4ExactSlabStarFullActionProbe.fullData`,
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`, constructs
the ordinary weighted GNS form for the original complete action. But a
change of law also changes its conditional projections. Norm comparison
alone is not a comparison of those operators.

`BF4ExactSlabConnectedFaceResponse.covariance_response_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:224`, instead
compares adding an ENTIRE heat face. Its spatially summable signed response
bound remains open. This cutoff-change theorem does not discharge that
hypothesis, does not compare reflected OS norms, and does not supply spatial
separation. Do not expand it into further completion/operator wrappers
without identifying a concrete consumer.

## 3. Parallel review: why cap/floor is not yet a finite-volume OS gap

The available original interface bounds are
`BF4ExactSlabAllNomeSpatialHeatCertificate.interface_weighted_floor` and
`interface_weighted_upper`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:144`
and `lean/YMGap/Continuum/BF4ExactSlabAllNomeSpatialHeatCertificate.lean:151`.
Their constants are headFloor(w)^F and prefixCap(w)^F for the actual number
F of fixed faces, so volume dependence is explicit.

`BF4ExactSlabBoundaryMarginal.exact_bilinear_eq_boundaryHaar`,
`lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:100`, retains the
complete dressed boundary marginals and the actual interface. The all-nome
completed unit complement exists as
`BF4ExactSlabPlaquetteCenteredCompletion.UnitComplement`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteCenteredCompletion.lean:179`.

However, `BF4ExactSlabPlaquetteTimeEmbedding.translate`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeEmbedding.lean:39`, maps
`PlaquetteExpression half` to `PlaquetteExpression (half+n)`.
`BF4ExactSlabPlaquetteTimeCorrelations.correlation_pairing`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteTimeCorrelations.lean:99`, pins
the correlation inside the enlarged completion. Neither declaration
constructs stationary time powers on a fixed finite-volume carrier.

NOT FOUND in the temporal-Haar, boundary-marginal, finite-stage
time-embedding/correlation and completion modules reviewed: the all-nome
fixed-spatial-box stationary temporal-kernel/OS identity needed to call a
cap/floor contraction a physical finite-volume transfer gap. Moreover,
`BF4ExactSlabSelectedInterfaceCoercivity.selectedFloor_exponent`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedInterfaceCoercivity.lean:64`,
uses the observable-dependent selectedCutoff, not a common completed-space
constant.

The already-proved
`BF4ExactSlabThermodynamicCompletedGap.complement_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedGap.lean:99`,
is on the separate thermodynamic geometric-time completion at fixed nome
1/1024 (`BF4ExactSlabPlaquetteSmallNomeCertificate.nome`,
`lean/YMGap/Continuum/BF4ExactSlabPlaquetteSmallNomeCertificate.lean:32`).
It is not an all-nome finite-volume instance. This section is source review,
not a new proof or current-session recheck of those older declarations.

## 4. Verification and remaining goal

All 20 new public gates pass: 1 ratio, 6 rational variance, 13 original
variance. Dependencies are subsets of {propext, Quot.sound}. Seven focused
serialized one-worker/20 GiB checks were run: three helper checks and four
original-module checks, including one corrected syntax attempt, the
added null-space corollary, and two final rechecks. No limits were raised.

A timestamp check found that the cached SumOfSquares artifact predates its
source timestamp. A separate monitored dependency-complete target,
`+YMGap.Constructive.SumOfSquares:olean`, exited successfully with the
existing cache and no rebuild. An older timestamp alone therefore did not
establish stale content. RationalVarianceComparison and the original-action
consumer were then rechecked successfully; their gate logs were unchanged.
This is a narrow cache/build validation, not a fresh elaboration of every
transitive dependency.

Final local log SHA-256 values:

- `/tmp/ym-rational-positive-ratio.log`:
  `e9c69f64cfd3bee612e632870805d5dc6ff9891a1eac7637976ce623ba79047d`.
- `/tmp/ym-rational-variance-comparison.log`:
  `fe1ea4561a84a6be2e7ae1487e30d4ec9525314752499f9f0e7a9f8618e21de9`.
- `/tmp/ym-original-one-face-variance.log`:
  `9ceaff42727122e5f7e0b102922a41e7cb3c9819b282813576dc6fb3fffc887d`.

Three root imports added; root/full-tree build and full audit unrun.
No old theorem statement, canonical field, custom axiom or literal hole
changed. CI remains manual-only. The next spatial estimate, same-object
physical time/scale control, continuum QFT/nontriviality and all compact
simple groups remain open. The goal remains active.
