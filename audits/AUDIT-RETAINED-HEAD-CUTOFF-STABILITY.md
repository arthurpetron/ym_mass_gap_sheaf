# Original one-face cutoff stability and retained-head correlation

Date: 2026-09-15 (local). Parent checkpoint: `fe9cb83`.

## Whole-project goal and this checkpoint's scope

Construct the nontrivial continuum Yang--Mills theory and positive physical
mass gap required by Clay for every compact simple gauge group, within the
repository's constructive witness/modulus/axiom contract. The action,
observables, OS reconstruction, time and Hamiltonian must be the SAME theory.
The whole-project target remains OPEN.

This checkpoint proves a local representation-cutoff estimate and packages
an actual retained-head counterexample to discarding its connected baseline.
It proves neither spatial decay nor a spectral gap. No canonical frontier
field or old theorem statement changes.

## Parallel work and the mathematical contraction

Two independent proof branches supplied rational determinant algebra and
the positive retained-tube witness. The parent supplied the original-action
consumer; a separate read-only review checked the endpoint accounting,
normalization, uniformity and existing connectedness consumers. Only the
parent compiled, one check at a time.

For an arbitrary fixed positive background B, write H for original Haar,
h for the original face prefix at K and h' for that prefix at K+L. Set
z=H(Bh), Z=H(Bh'), a=H(pBh), A=H(pBh'). No spectator independence is assumed.
The same positive heat floor applies at BOTH endpoints. Consequently the
absolute tail bound eta*headFloor(w) gives

```
|A-a| <= c*eta*Z,    |Z-z| <= eta*Z,    |a| <= c*z
A*z-a*Z = (A-a)*z-a*(Z-z)
|A*z-a*Z| <= 2*c*eta*(Z*z)
|A/Z-a/z| <= 2*c*eta
```

The new-partition relative errors avoid a 1/(1-eta) loss; no eta<1 guard is
needed. The original background specialization constructs positivity from
all its actual heat factors. It does not assume a new analytic input.

| Declaration | Source | Checked content |
|---|---|---|
| `relative_determinant_bound` | `lean/YMGap/Continuum/RationalRelativePerturbation.lean:27` | Rational endpoint-relative determinant estimate, no inversion. |
| `mass_difference_bound` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:79` | Partition error paid relative to the later original partition. |
| `moment_difference_bound` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:91` | Same for a probe with supplied polynomial interval cap c. |
| `old_moment_bound` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:112` | Original moment bounded relative to the old partition. |
| `determinant_bound` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:121` | Keeps both different partitions and every shared variable. |
| `faceMass_positive` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:134` | Strict positivity from a positive-mass certified background. |
| `normalized_difference_bound` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:139` | Normalized 2*c*eta estimate for any such background. |
| `original_background_determinant` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:152` | Actual spectator heat product at its own late cutoff J. |
| `original_background_normalized` | `lean/YMGap/Continuum/BF4ExactSlabOneFaceCutoffStability.lean:165` | Actual normalized specialization; background positivity constructed, not assumed. |

## Exact parameter and uniformity boundary

Required: rational 0<w<1, eta>0, a physical face id, K>=relativeCutoff(w,eta),
and a supplied `Interval` certificate for the fixed probe p with cap c.
The generic background has a square certificate and positive Haar mass.
For the original-product specialization, every listed spectator face is
physical and its cutoff J>=headCutoff(w). The list may include repetitions;
only the displayed single factor changes. A once-per-face full action
requires choosing the complementary list without a duplicate changed face.

`relativeCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:139`, is
max(headCutoff(w), tailCutoff(w,eta*headFloor(w))). `headFloor` and
`headCutoff` are defined at lines 50 and 55 of that file. The coefficient
2*c*eta has no extent, background-size, K, J or L factor; the threshold
still depends on w and eta, and the coefficient is uniform only for a
uniformly supplied probe cap. This is NOT a coupling-uniform cutoff,
distance-decay estimate, or physical-scale mass bound.

The rational determinant algebra is group-agnostic. Its concrete consumer
uses the existing SU(2) original heat polynomials and positive certificates.
A group-agnostic local cutoff-stability estimate is not a group-agnostic
Yang--Mills gap claim.

## Why retaining the head changes the connectedness problem

The old connected-selection cancellation concerns selected WHOLE action
faces: `connectedCoefficient`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedSelectionExpansion.lean:57`,
and `coefficient_zero_of_separator`, that file at line 83. It requires a
separator of those interacting factors. It is not a theorem that connected
coefficients vanish whenever only the added tails fail to connect probes.

The new witness retains the original twelve-face tube product, all cutoff
spins and the unchanged three-step endpoint probes:

| Declaration | Source | Checked content |
|---|---|---|
| `cutoff` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:40` | Computed max(1,headCutoff(w)). |
| `headPolynomial` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:47` | Literal ordered original tube heat product. |
| `headCertificate` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:51` | Positive certificate for that same retained head. |
| `connectedHead` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:57` | Original connected numerator, including both replica means. |
| `connectedHead_eq` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:62` | Exactly w^36, reusing `original_tube_numerator`. |
| `connectedHead_pos` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:71` | Strict positivity for w>0. |
| `connectedHead_ne_zero` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:76` | Cannot be replaced by zero. |
| `original_endpoint_separation` | `lean/YMGap/Continuum/BF4ExactSlabRetainedHeadCorrelation.lean:84` | Original endpoint time coordinates differ by three. |

This evaluates the named tube SUBACTION, not the full slab and not a new
tail expansion. At the source-review level, `FiniteSelectionMobius.coefficient`,
`lean/YMGap/Continuum/FiniteSelectionMobius.lean:25`, has empty coefficient
f[]. Therefore an expansion about this head cannot discard its baseline
merely because no additional tail has been inserted. The new module does
not assert a full-slab lower bound or a general head-relative expansion.

## Actual next consumer and open residue

The existing `covariance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeCovariance.lean:153`, consumes an
original connected-numerator estimate relative to its SAME partition square.
The distance producer `full_connectedNumerator_distance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabTwoProbeDistanceDecay.lean:79`, still has
the old small-nome and summability guards. No new input to that spatial
producer is discharged here. The new local result controls a single
head-to-later-prefix change, not addition/deletion of a whole interaction.

The mathematical residue is control of the retained head's connected
covariance and its response to tail insertions with usable spatial decay.
Finite telescoping of local errors incurs a face-count factor; it alone
does not supply volume-independent control of arbitrarily many changed
faces. The prior unit-reference obstruction remains:
`no_eventual_small_intervals`,
`lean/YMGap/Continuum/BF4ExactSlabHeatHaarGuardObstruction.lean:340`.

Varying-nome thermodynamic compatibility, physical time/spacing calibration,
continuum QFT and nontriviality, and every compact simple gauge group remain
open. There is no Markov-gap-to-OS-gap substitution in this increment.

## Verification boundary

Five focused safe launches (one rational helper, three integration checks
including two syntax/namespace/parameter corrections, one head witness),
serialized with one worker and the unchanged 20 GiB ceiling. All final 19
public gates (1+8+10) are within {propext, Quot.sound}; no sorryAx or
classical/native shortcut. No dependency rebuild or raised limits.
Final logs are clean. Direct imports used cached artifacts; unchanged
transitive dependencies were not rebuilt or comprehensively re-audited.

Final log SHA-256 values:

- `/tmp/ym-relative-perturbation.log`:
  `6fc7d00f1bcebfb0210f6f835619996bc59b96bc74c9f0b787e97523212664d8`.
- `/tmp/ym-one-face-cutoff-stability.log`:
  `4df12a3ebbb95ddcf4d450d7d0861fdcbb7ba408c1140e0ffa33ab9be0afe0fe`.
- `/tmp/ym-retained-head-correlation.log`:
  `d7bab0e1aa030630d9d16c93bb4b3aaa1d428ac2d02721abde30e47b18545a3e`.

Three semantic-root imports added; root/full-tree build and full audit not
run. CI remains manual-only. No old theorem statement, canonical frontier
field, custom axiom or literal hole changed. Goal remains active.
