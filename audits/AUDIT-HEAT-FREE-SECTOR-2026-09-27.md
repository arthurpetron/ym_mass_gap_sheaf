# Neighboring conditional updates: the free-centered sector is not invariant

Date: 2026-09-27. Base: `e9d238f`.

## Causal question

Can the existing strict local bound be iterated to leave the old small-nome
spatial regime, simply because each update is conditional and the input is
globally centered? The general inference is false. A new exact positive
two-site SU(2) heat example has BOTH input centerings, but its neighboring
conditional update loses free-link centering.

This is not a counterexample for the full physical slab, gauge-invariant
Wilson probes, spatial mixing itself, or Yang--Mills. It rules out an
automatic sector-preservation argument from the displayed properties alone.

## Kernel-checked example

Let y be block 0, x block 1, a=w^3, and h the original relative heat packet
including every spin through K. Retain the endpoint B(x)=1+x_0/2 and use

    W(y,x) = h(y,x)*B(x),       f(y,x) = x_0*(y_0-2*a).

The existing heat marginal gives total W mass one. B has a certified floor
1/2. For 0<w<1 and K>=max(1,headCutoff(w)), the complete W has a constructed
positive certificate and the following identities hold:

- Free Haar integration in x annihilates f coefficientwise.
- The W-weighted global mean of f is zero.
- The actual `conditionalHeat` output reproduces every tail test under W
  with its B-weighted tail marginal. Thus B is retained, not dropped.
- Its B-weighted global mean is still zero.
- Its FREE Haar mean in x is a/4, strictly positive.

The proof computes conditional pairings using coordinate transmission;
it does not require raw coefficient equality with a guessed output.
The source-pairing formula is that of a*x_0^2-2*a*x_0. Its moments use
H(x_0^2)=1/4, H(x_0*B)=1/8, and H(x_0^2*B)=1/4.

Declarations in `lean/YMGap/Continuum/SU2QuaternionHeatFreeSectorObstruction.lean`:

| Declaration | Line | Evidence |
|---|---:|---|
| `source_supported` | 71 | The actual input is a supported polynomial on two quaternion blocks. |
| `endpoint_floor` | 77 | Constructed B-1/2 certificate. |
| `weight_certificate` | 93 | Constructed positivity of the SAME h*B, with late-cutoff guards. |
| `weight_mass` | 102 | The actual complete weight has mass one. |
| `source_free_centered` | 106 | The OTHER endpoint's free conditional mean is zero. |
| `source_pairing` | 125 | Exact all-test calculation retaining every heat spin. |
| `output_weighted_pairing` | 157 | Original-weight conditional identity against every tail polynomial. |
| `source_weighted_mean_zero` | 170 | Actual input global centering, not free-measure centering alone. |
| `output_weighted_mean_zero` | 195 | Actual global centering is preserved by the update. |
| `output_free_mean` | 206 | Free output mean equals w^3/4. |
| `output_not_free_centered` | 223 | That free mean is nonzero for w>0. |
| `free_sector_preservation_false` | 235 | Refutes the automatic preservation implication even for globally centered inputs. |

The algebraic counterexample declaration requires only w>0 and K>=1.
Its positive-law subcase additionally uses w<1 and K>=headCutoff(w), via
`weight_certificate`; truncated heat positivity is not claimed for all K>=1.

## Source review and next requirement

Two Sol reviews independently inspected the available alternatives. The
original full-action `conditionalProjection` is constructed in
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalProjection.lean:220`.
Its locality is recorded by `conditionalProjection_localRepresentative` in
`lean/YMGap/Continuum/BF4ExactSlabStarConditionalLocality.lean:141`.
The strict `conditionalProjection_freeResidual_norm` estimate in
`lean/YMGap/Continuum/BF4ExactSlabStarLocalInfluence.lean:134` covers a
specified star-deleted/free-centered sector, not every globally centered input.

The new example does not identify its endpoint action with that full slab's
deleted-star action. It prevents supplying the missing preservation premise
by a universal claim about conditional updates and global means. A
source-specific full-action preservation proof is not refuted; it is still
absent. No block-scale original-action mixing criterion was found in the
reviewed conditional-projection, local-influence, transfer-mixing and rooted
response modules. This is source-review evidence, not a nonexistence theorem.

NEXT: any conditional route must estimate neighboring-sector leakage or use
an interacting block-centered sector with a proved iteration law. It must
then join to the original normalized signed response, not merely a Markov
dynamics gap. The direct existing consumer is
`covariance_response_bound_of_rooted` in
`lean/YMGap/Continuum/BF4ExactSlabRootedResponseResummation.lean:118`.
`response_distance_activity` in
`lean/YMGap/Continuum/BF4ExactSlabResponseDistanceActivity.lean:127` retains
the exact signed activity and normalization but does not estimate it.
Neither the new diagnostic nor another local-floor wrapper supplies a
spatial estimate useful along a changing-coupling physical-spacing family.

## Verification

Final focused monitored check: exit 0, 0.99 seconds, one worker, 20 GiB cap.
All 12 public gates report only {propext, Quot.sound}; no warnings. Initial
checks exposed namespace, rational-normalizer and padded-unit representation
issues; these were corrected without changing the mathematical statements.
Sol separately reviewed the final source and its positive-law/conditional
identification. No competing Lean process, broad build/audit, new hole,
canonical field change, or broad chart-marker advance. No literature refresh.
The continuum/all-group Clay target remains open.
