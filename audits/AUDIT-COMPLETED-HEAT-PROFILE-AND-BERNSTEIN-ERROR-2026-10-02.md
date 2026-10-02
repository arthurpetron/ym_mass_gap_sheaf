# Original completed heat profile and explicit coefficient error

Date: 2026-10-02 UTC. The forward original-profile estimate and the backward
numerical coefficient estimate are now proved, not assumed analytic inputs.
They do not yet meet in an original Haar certificate. The continuum Clay
target remains OPEN.

## Forward: the original completed heat kernel

For 16/17<=q<1 and EVERY rational -1<=x<=1, including both endpoints,
`pointwiseHeat_chord_quartic_bound`,
`lean/YMGap/Continuum/SU2HeatJacobiCompletedProfileBound.lean:280`, proves

    [2(1-x)]^2 K_q(x) <= 40*24576^2*(1-q)^2 K_(q*q)(x).

The order is sound eventual `CReal.leEv`. K is the EXISTING
`SU2PointwiseHeatSpacingCompletion.pointwiseHeatCReal`, with its original
spacing-dependent completion, not a substituted positive kernel. The nome
dependence remains explicit; this is not a physical mass calibration.

| Declaration | Source line in `lean/YMGap/Continuum/SU2HeatJacobiCompletedProfileBound.lean` | Constructed estimate |
| --- | --- | --- |
| `thetaProduct_nome_gap_bound` | 93 | Original completed theta profile, coefficient 2*24576^2*(1-q)^2. |
| `sFactor_nome_widening` | 157 | q*S_q<=5*S_(q*q), for ALL strict nomes and x>=-1. |
| `Rproduct_nome_gap_bound` | 180 | Original theta/derivative product comparison, coefficient 10*24576^2*(1-q)^2. |
| `original_heat_product_pin` (private) | 220 | R_q is equivalent to 2*q*K_q, by the proved original differentiated Jacobi identity. |
| `pointwiseHeat_nome_gap_bound` | 242 | (1-x)^2*K_q<=10*24576^2*(1-q)^2*K_(q*q). |
| `pointwiseHeat_chord_quartic_bound` | 280 | The displayed original chord estimate. |

The finite product estimate passes through the actual completed products.
The proved height bound and original positive widened theta height permit
cancellation. The actual paired S estimate passes using monotonicity of its
original partial sums. The original heat pin then cancels the SAME positive
rational factor 2*q*q. No reciprocal of a heat minimum is used.

## Backward: the actual normalized falling coefficient

At N=n+1 define A=product(n,j,r), B=product(n,N,r), P=(j/N)^r and
e=C(r)/N, using `BernsteinFallingProductError`'s actual recursive products
and triangular error coefficient. The new module constructs

    B >= 1/2 > 0,
    P <= A/B+e,
    A/B <= P+2e.

| Declaration | Source line in `lean/YMGap/Continuum/BernsteinNormalizedFallingProductError.lean` | Constructed data/estimate |
| --- | --- | --- |
| `denominatorCutoff` | 32 | Existing explicit rational modulus at tolerance 1/2. |
| `topProduct_half_floor` | 34 | Actual denominator floor at every later n. |
| `topProduct_positive` | 48 | Positive denominator derived from the floor, not supplied. |
| `normalizedProduct` | 54 | Actual constructive rational quotient A/B. |
| `normalizedProduct_mul_top` | 57 | Exact quotient-times-denominator identity. |
| `power_le_normalizedProduct_error` | 68 | Reverse error at most e. |
| `normalizedProduct_le_power_error` | 82 | Forward error at most 2e. |
| `toleranceCutoff` | 116 | Computed maximum of denominator safety and the modulus at epsilon/2. |
| `normalizedProduct_close` | 121 | Both errors <=epsilon for every later n and every 0<=j<=n+1. |

Orders r=0,1 and truncated numerators j<r remain covered. This constructs
numerical coefficient errors, not a rational Bernstein reconstruction or
an original Haar square witness.

## Exact remaining join

`affine_original_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135`,
still requires the Type-valued ORIGINAL `Certificate` of the polynomial
c*heatPrefix(q*q,K)+cap(error)-chord^2*heatPrefix(q,K), at the SAME original
source, cutoff and partition. Pointwise completed positivity is not that
certificate. Explicit original finite-prefix tails, rational Bernstein
coefficient reconstruction and the original scalar-substitution square
witness remain to be composed.

Nor does the positive-source affine consumer estimate the signed centered
whole-word cross terms. Useful comparison to OWN interacting variance on
a justified changing family remains OPEN. Nonzero continuum survival,
physical mass calibration, full SAME-theory OS/QFT and every compact simple
group remain OPEN. No exact canonical chart claim changes.

## Verification

Two final focused checks passed, one worker at a time, with an explicit
20-GiB hard ceiling and 12-GiB OS reserve. Fresh dynamic preflights reported
85 percent pressure-free memory and zero swap. All 15 public gates are
within {propext,Quot.sound}; no accepted log has errors, warnings, sorryAx
or Classical.choice. Independent mathematical reviews passed both sources.

The rejected first checks were local elaboration errors: a decision involving
a free approximation index, and a representation-sensitive rational `change`.
Closed rational decision and existing constructive order transitivity repair
them without changing theorem types. Rejected logs are not proof evidence.

Accepted logs:

- `/tmp/ym-jacobi-completed-profile-20261002-second.log`
- `/tmp/ym-bernstein-normalized-error-20261002-second.log`

| Artifact | SHA256 |
| --- | --- |
| Completed-profile source | `4d89424de197be83e19c36851c303041408cb0285087cce98a499c5d3a4f09d4` |
| Normalized-error source | `e0d82fd571fc06a82cde76b7eaa57f87038b3e9f435ca41c68b96926f5be64d0` |
| Completed-profile log | `1bfd0738f7b54d917319d0d12cdf734e0a9be6cacb8a4f10c706a42917109444` |
| Normalized-error log | `8fb592f7074cb9900546ed63d3b4013b1c89563eaa8c012dd0cad75d75e3c5b6` |

Two root imports are registered, not aggregate-checked. No broad root/tree,
guard or audit was run. No new sorry, axiom, classical shortcut, weakened
frontier, surrogate action, resource ceiling or CI change was introduced.
The canonical chart block is unchanged and is not reprinted.
