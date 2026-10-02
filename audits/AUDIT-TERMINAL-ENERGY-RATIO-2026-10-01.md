# Original terminal-depth energy / OWN-variance reduction

2026-10-01 UTC. Constructed original edge comparisons and a conditional
reference-depth consumer. No reference analytic estimate, changing-scale
bound, continuum endpoint or Clay field has been discharged.

## Exact new mathematical result

Fix strict nome 0<w<1, spatial width and late heat cutoff K. Let
g_n=T^n(1) be the ORIGINAL finite terminal message. Its actual edge density is

    mu_n(x,y) = K(x,y)V(x)V(y)g_n(x)g_n(y).

Here K(x,y) denotes the original kinetic polynomial, not the integer cutoff.
`terminalMessage` is defined at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:118`;
`edgeDensity` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:55`.
The two original spatial factors and original transfer are retained.

For n=s+1+r and m=s+1+t, the constructed `terminalComparison` at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:230`
has positive lower endpoint l, upper endpoint u, and relative width

    u-l <= eta*l, eta = comparisonKappa(w,width)*mixRate(w,width)^s.

The endpoint positivity and relative width are proved by
`terminalComparison_lower_positive` at that file's line 256 and
`terminalComparison_relative_width` at line 306. `comparisonKappa` at line 81
is (kineticCap/kineticFloor)^2; `comparisonEta` at line 94 is the displayed
geometric error. Both retain strict nome and width dependence.

Multiplication of ACTUAL square certificates gives

    l^2 mu_m <= mu_n <= u^2 mu_m.

For every supported signed polynomial f, let Eraw_n be the ORIGINAL raw
temporal energy and S_n=Z_n*OWNVariance_n its raw centered marginal variance.
The new certificates imply

    Eraw_n <= u^2 Eraw_m, l^2 S_m <= S_n.
    Eraw_m <= c S_m  ==>  Eraw_n <= c(1+eta)^2 S_n, for c>=0.

The variance centers can DIFFER. The proof tests the reference density at
the later density's explicitly computed mean, then uses its own minimizing
center. No absolute-value termwise decomposition or common-mean hypothesis
occurs. Zero variance and c=0 are allowed; neither variance nor l is inverted.
After division by the later ORIGINAL positive Z_n, this is

    normalizedEnergy_n <= c(1+eta)^2 OWNVariance_n.

There is NO extra partition-factor loss. The analytic input is the reference
ratio itself; terminal positivity and relative comparison are constructed.

## Declaration-to-consumer map

| Declaration | Module:line | Exact role |
| --- | --- | --- |
| `rawVariance`, `rawVariance_own_mean` | `lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.lean:36`, `:51` | Actual density mass times OWN variance equals its own centered square. |
| `rawVariance_le_shifted`, `rawVariance_nonnegative` | `lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.lean:69`, `:85` | Any rational center bounds the own minimizer; its raw value is nonnegative. |
| `raw_square_comparison`, `raw_variance_comparison` | `lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.lean:107`, `:124` | Literal density-order certificate controls supported raw squares and OWN raw variance. |
| `energy_variance_ratio_transport` | `lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.lean:143` | Division-free scalar composition of energy upper, variance lower and relative bracket width. |
| `edgeLowerCertificate`, `edgeUpperCertificate` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:144`, `:174` | Construct original two-end edge order with squared bracket endpoints. |
| `energy_upper` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:206` | Original jump-square identity transports raw temporal energy. |
| `edgeMass_positive`, `edgeMoment_pin`, `rawEdgeVariance_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:237`, `:244`, `:258` | Construct the original positive denominator and pin edge moments/OWN variance to the original odd chain. |
| `terminal_ratio_transport`, `finite_reference_all_later` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:285`, `:359` | Actual original ratio transport; t=0 reduces reference depth to ONE s+1. |
| `comparisonOnset`, `comparisonEta_small` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:371`, `:377` | Computed geometric prefix for every supplied positive error budget, valid at all later prefixes. |
| `referenceCoefficient`, `finite_reference_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:42`, `:52` | Same signed radius-zero Wilson source; all-late-cutoff reference ratio controls every later depth. |
| `finite_reference_diagonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:77` | Explicit regulator onset max k0 (s+1). |
| `energyLimit_reference_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:103` | Uses the EXISTING energy and variance QCauchy witnesses; no new convergence premise. |
| `completed_reference_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:123` | Original completed one-step time loss versus SAME ambient centered norm. |

The final completed pins are `energyLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218` and
`varianceLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236`.
Their recipient is B(v,v)-B(v,T(1)v) versus D*B(v,v). The original AMBIENT
norm is not replaced by the bond norm, which has a different carrier/quotient.

## Exact reduced frontier and parameter boundary

`completed_reference_ratio` assumes only the stated reference inequality,
with supplied c>=0 and onset k0, for every cutoff offset k>=k0 at ONE terminal
depth s+1. Its coefficient D=c*(1+comparisonEta(w,width,s))^2 has NO cutoff
or later-depth argument. The reference premise itself is NOT proved here.
`comparisonOnset(w,width,epsilon)` computes s with eta<=epsilon for every
epsilon>0; it is NOT width- or nome-uniform.

The source polynomial, actual marginal mean, original action and transfer,
both partitions and completed carrier agree through every join. The result
allows signed/repeated Wilson expressions, but supplies no assertion that
an arbitrary expression satisfies a small reference ratio. It neither
removes the existing fringe kernel nor constructs changing-width maps.

The useful signed reference estimate on a justified changing family remains
OPEN, as do original cross-scale compatibility, spatial/spacing control,
nonzero continuum survival, finite positive physical mass, full same-theory
QFT, every compact simple group and Clay. This is an UPPER energy/norm
estimate (response/survival direction), NOT a LOWER spectral-gap floor.
The generic positive-source scaling shortcut obstruction is unchanged.
All exact canonical chart claims retain their previous state.

## Verification boundary

Focused commands, serialized from the repository root:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/QuaternionHaarDensityVarianceComparison.olean --log-file /tmp/ym-raw-variance-comparison-final-20261001.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.olean --log-file /tmp/ym-terminal-energy-comparison-onset-20261001.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.olean --log-file /tmp/ym-terminal-reference-completed-final-20261001.log
```

All exit 0; 7+10+5=22 printed public gates, all {propext,Quot.sound}.
No error, warning or sorryAx in these final logs. No new sorry, axiom,
Classical shortcut, native checker, witness erasure, analytic bundle or
weakened frontier. One capped worker, 20-GiB ceiling, 12-GiB OS reserve and
continuous safety telemetry. Parallel proof/review work used no concurrent
Lean workers. CI and chart unchanged.

Sol independently developed the own-center comparison and completed consumer.
Luna reviewed the actual edge/mean/depth/partition joins, explicit modulus,
all 22 source/log gates, hashes, citations and upper-bound scope. Both reviews
passed; kernel verification remained serialized by the parent.

| Artifact | SHA-256 |
| --- | --- |
| `QuaternionHaarDensityVarianceComparison.lean` | `14cfd078594f62eafea9a272103592ffa700c964fbdeef4a86dc931ff0858b8a` |
| `BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean` | `f4821831939cbee54ba31823ddf2b07305d5b223eb4ba48f0a25ee7dc88a107e` |
| `BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean` | `1b3b87c8d1fe7c621b98e64f37dea61c5ad8625c04206462bca661722081f3cb` |
| `/tmp/ym-raw-variance-comparison-final-20261001.log` | `363c064ca4bce2451d07b8c846e976e723b61140ee7873400dfd0c7eea634c4e` |
| `/tmp/ym-terminal-energy-comparison-onset-20261001.log` | `14aad77acaf1db78f5a1d0dba36a8741ed38a17198fb8a1b9c1c8b7ccf8fc19f` |
| `/tmp/ym-terminal-reference-completed-final-20261001.log` | `f69b25982407bcc602a4f689c0ad0f8a3b6e43d9f4ce61509478f6849320c1d5` |

Earlier draft/verified-named logs include failed elaborations or earlier
sources and are NOT final evidence. Missing namespace/explicit arguments,
opaque-definition pins and include/docstring placement were repaired;
limits were not raised. Three semantic root imports added, but the full
root/tree build, axiom audit, guard and progress-metric script were NOT run.
