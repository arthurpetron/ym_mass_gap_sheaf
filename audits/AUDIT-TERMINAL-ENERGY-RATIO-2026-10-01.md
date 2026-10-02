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

## Finite original reference margin certificate (2026-10-02 UTC)

The all-late-cutoff input at ONE reference depth now has a sufficient finite
certificate, with its cutoff errors constructed from the original source.
At fixed t=s+1 and c, write J for the actual originalWindowScalar and define

    S = J(squareAt e 1), P = J(crossOdd x x),
    U = J(crossOdd x unit), L = J(crossOdd unit x),
    alpha = (c-1)/2,
    g = c*OWNVar-E = alpha*S + c*(P-U*L).

Here x is the literal radius-zero singleSlice(e). E=S/2 and OWNVar=E+P-U*L
are the existing actual energy/variance pins; BOTH finite means and the SAME
partition remain. This applies to signed original expressions, not merely
a diagonal plaquette or positive coefficients. No measure is substituted.

The original window bounds give a common endpoint cap B>=1. Let
A=abs(alpha)+abs(c)*(1+2B) and delta=epsilon/(1+A). The signed margin is kept
intact; absolute values enter ONLY the cutoff error. Four windowCutoffCauchy
moduli at delta and the SAME fixed t supply a computable maximum M(epsilon).
The product error is at most 2B*delta, so the total margin error is at most
A*delta<=epsilon. No time threshold or assumed convergence field enters.
The denominator remains positive at c=0, and no variance division occurs.

The finite decidable check requires c>=0, epsilon>0, pivot>=M(epsilon) and
g(pivot)>=2epsilon. Acceptance proves g(k)>=epsilon and E(k)+epsilon<=c*OWNVar(k)
for EVERY k>=M(epsilon). It then feeds the existing original terminal-depth
transport and completed_reference_ratio, with coefficient c*(1+comparisonEta)^2.
Acceptance implies c*OWNVar(k) is not zero and OWNVar(k) is not zero. Thus a
zero-variance/vacuum test cannot supply this certificate. No certificate for
a physical changing family is constructed here. The positive-margin criterion
is sufficient; no equivalence for zero-slack estimates is asserted.

### Declaration map

All new declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean`:

| Declaration | Module:line | Role |
| --- | --- | --- |
| `referenceMargin_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:74` | Exact signed combination of FOUR original windows. |
| `cutoffTolerance` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:136` | Computed positive-denominator error budget. |
| `referenceCutoff` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:143` | Maximum of four fixed-depth cutoff moduli. |
| `referenceMarginCauchy` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:222` | Actual cutoff-only joint-margin control. |
| `check` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:267` | Executable finite rational/natural test. |
| `Certificate.margin_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:300` | Positive margin at every later cutoff. |
| `Certificate.reference_strict_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:308` | Retains the absolute slack. |
| `Certificate.all_later_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:324` | Existing original terminal-depth transport. |
| `Certificate.completed_ratio` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:332` | SAME completed time loss / AMBIENT centered norm. |
| `Certificate.product_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:346` | Rejects zero coefficient-times-variance. |
| `Certificate.variance_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean:358` | Non-vacuous original finite variance. |

The source pins are finiteEnergy_half_pin at
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:124`,
finiteVariance_budget_pin at
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:119`, and
finiteScalar_connected_pin at
`lean/YMGap/Continuum/BF4WilsonAllNomeCenteredTransferBondLimit.lean:177`.
The cutoff producer is windowCutoffCauchy at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonWindowJointCauchy.lean:36`.

### Verification and residue

Focused command, serialized from the repository root:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4WilsonAllNomeFiniteReferenceMargin.olean --log-file /tmp/ym-finite-reference-margin-20261002-final.log
```

Exit 0. Eleven printed public gates, all {propext,Quot.sound}; no error,
warning or sorryAx in the final log. No new sorry, axiom, Classical shortcut,
native oracle, analytic convergence input, witness erasure or weakened
frontier. The one-worker 20-GiB ceiling and 12-GiB OS reserve were unchanged.
Pre/post memory pressure reported 86% free, swap zero; no compiler survived.
Earlier draft, second and third logs contain failed elaborations and are NOT
verification evidence. Namespace, notation-binder, include/docstring and
rational-as-polynomial-variable issues were repaired without raising limits.
Sol independently reviewed the actual algebra, crossed product caps, four
fixed-depth moduli, checker soundness and scope. Luna independently checked
the final source/log gates, hashes, declaration citations, nonzero-variance
consequence and documentation scope. Both reviews passed. Absolute slack is
preserved at the reference depth across cutoff; later-depth/completed consumers
use the non-strict ratio, not a claimed transport of that absolute slack.

| Artifact | SHA-256 |
| --- | --- |
| `BF4WilsonAllNomeFiniteReferenceMargin.lean` | `e557ef967b1fc2ef447fcdec08d40316f45b7a23d42507fa3d842cb9786f2191` |
| `/tmp/ym-finite-reference-margin-20261002-final.log` | `b96ce07276014b18732e830ef2b3c665ad03fc9df03169043895d7ee738c5773` |

NEXT: produce accepted finite data with useful c on a justified original
padded/changing family, or prove the source-specific estimate which certifies
them. No successful certificate or feasible runtime for a physical instance
was established. The finite-window/mean caps and modulus retain source, nome,
width and fixed-depth dependence. Cross-scale pairings, spatial/spacing control,
nonzero continuum survival, finite positive physical mass, full same-theory
QFT, every group and Clay remain OPEN. This is an UPPER energy certificate,
not a lower physical-gap theorem. One semantic root import added; the full
root/tree/build/axiom-audit/guard and progress-metric script were NOT run.
CI and exact canonical chart claims unchanged; no ASCII reprint.
