# Computed harmonic decomposition in the original product-map pairing

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with same-theory QFT axioms, isolated vacuum and finite positive physical
mass gap. This increment is exact finite SU(2) polynomial mathematics,
not a spectral-gap or continuum estimate.

## Removed input assumption

The preceding selected-factor theorem required the caller's input to be
homogeneous and harmonic. The new consumer
`productMap_selected_expansion`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:158`,
requires only finite support of the arbitrary signed input p and upper
test g, valid remaining kinetic indices, and absence of the selected
index from that remaining list. It COMPUTES the needed harmonic modes.
No harmonicity, degree, decomposition or propagation premise is supplied
for p.

Let C_i denote the explicit pair-exposing swaps, let h_j be the computed
signed harmonic parts of C_i(p), and let d_j be their head degrees. With
R the product of every remaining kinetic factor times the lifted g, the
checked formula is

    H_n[g * productMap(n,w,K,i::ids,p)]
      = sum_j (if d_j <= K then
          w^(d_j*(d_j+2)) * H_(2n)[retainedImage(h_j) * C_i(R)]
        else 0).

The right side stays in the explicit selected chart on the same doubled
carrier. The coefficient, sign and tail variables of each mode are kept.
The entire remaining insertion C_i(R) is retained. This is not a
simultaneous diagonalization of the interacting transfer or of every
remaining kinetic factor.

## Constructive mathematical argument

1. `headComponent` filters exact head degree. A computed finite range
   contains every term, and `headComponent_reassembly` proves coefficient-
   exact reassembly. Filtering inherits support and all per-term padding
   predicates; it makes no harmonicity assertion.
2. In four head coordinates, the full Laplacian product rule and Euler
   identity give

       Delta(r^2 p) = r^2 Delta(p) + 4(d+2)p.

   For a harmonic homogeneous h of degree d, iteration gives

       Delta(r^(2(k+1)) h) = 4(k+1)(d+k+2) r^(2k) h.

   The integer denominator is explicitly positive.
3. `decomposeHomogeneous` recursively decomposes the syntactic active
   Laplacian, whose degree drops from n+2 to n. `Mode.raise` integrates
   each resulting radial-harmonic term using that denominator. If q is
   their sum, Delta(q)=Delta(p), so h=p-q is harmonic and h+q=p. The
   returned finite list carries its actual polynomials, rational signed
   coefficients, degrees, support, harmonicity and exact reassembly.
4. An arbitrary supported input is identity-reindexed inside its declared
   carrier before splitting. This supplies the required padding. The
   existing prefix-to-Haar theorem, with BOTH support guards, identifies
   it with the original input. Radius powers are then removed only by
   the proved Haar sphere identity under arbitrary insertions.
5. The original all-label heat reproduction theorem is applied to each
   computed harmonic part. Explicit swaps and `productMap_pairing`
   return the formula to the actual product-map consumer above.

### Padding is part of the proof, not an identification by convention

Raw coefficient equality distinguishes `[0]`, `[0,0]` and longer zero
exponent lists. Thus the raw assertion Delta(radius)=8*polyOne is not
used. `laplacian_radius_mul_first` proves the required multiplication
identity for a polynomial whose exponent lists have length at least four.
This minimum length survives differentiation, sums, scalar multiplication
and radial lifting. Arbitrary input enters through the supported identity
reindexing/Haar bridge; no tail variable is silently discarded.

## Source map

| Declaration | Source | Checked content |
| --- | --- | --- |
| `headComponent_reassembly` | `lean/YMGap/Continuum/SU2QuaternionHeadHomogeneousComponents.lean:194` | Exact finite homogeneous splitting. |
| `laplacian_radius_mul` | `lean/YMGap/Continuum/SU2QuaternionFischerRadial.lean:82` | General radial product rule, not assuming p harmonic. |
| `radialFactor_positive` | `lean/YMGap/Continuum/SU2QuaternionFischerRadial.lean:172` | Explicit nonzero denominator. |
| `laplacian_radiusIter` | `lean/YMGap/Continuum/SU2QuaternionFischerRadial.lean:181` | Exact radial antiderivative coefficient. |
| `Mode.raise_laplacian` | `lean/YMGap/Continuum/SU2QuaternionFischerDecomposition.lean:79` | Computed lift differentiates to the original mode. |
| `decomposeHomogeneous` | `lean/YMGap/Continuum/SU2QuaternionFischerDecomposition.lean:136` | Witness-returning terminating Fischer recursion. |
| `paddedInput_carrier` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:103` | Padding preserves the supported original Haar carrier. |
| `modes_reassembly` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:112` | Coefficient equality to the explicitly padded input. |
| `modes_degree_le_cutoff` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:119` | Computed bound on every produced harmonic degree. |
| `polynomial_harmonic_carrier` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:158` | Arbitrary-insertion original-carrier harmonic expansion. |
| `polynomial_heat_pairing` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:198` | Original packet acting on any supported signed polynomial. |
| `polynomial_heat_pairing_above_cutoff` | `lean/YMGap/Continuum/SU2QuaternionPolynomialHarmonicExpansion.lean:211` | All modes of this fixed input survive above its explicit cutoff. |
| `selected_pair_expansion` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:58` | Arbitrary original pair; no input harmonicity premise. |
| `productHeat_selected_expansion` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:119` | All untouched factors remain. |
| `productMap_selected_expansion` | `lean/YMGap/Continuum/SU2QuaternionProductHeatHarmonicExpansion.lean:158` | Actual original lower product-map consumer. |

The recursion reuses the ALREADY existing `activeLaplacian`,
`lean/YMGap/Continuum/SU2QuaternionHeadDegreeDifferential.lean:93`,
and `activeLaplacian_degree` at line 106. A prior bounded inventory missed
that name; it has not been recreated.

## Exact residue and next mathematical target

The finite decomposition of arbitrary supported input is now constructed.
The remaining task is a quantitative, signed-mode energy comparison for
the actual weighted input, with repeated-factor compatibility where
needed. The full original endpoint correction must remain: see
`energy_eq_bare_add_correction`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGroundStateEnergy.lean:144`.
Bare harmonic orthogonality does not remove cross terms created by the
interacting endpoint weight.

The existing `partialHaarHead_harmonic_lower_degree`,
`lean/YMGap/Continuum/SU2QuaternionHarmonicDegreeSelection.lean:106`,
gives polynomial-valued cross-degree cancellation while retaining tails;
`partialHaarHead_harmonic_degree_bound` at line 129 covers a partner
with a lower degree bound. The computed list may contain MULTIPLE modes
of the same harmonic degree. These must be grouped with their signed
cross terms retained before any orthogonal norm sum is claimed. No new
norm/Pythagoras theorem or compatibility theorem for successive selected-
factor outputs is proved by this increment.

`modeCutoff` is the explicit degree-sum bound of the padded input. It is
not claimed independent of the input. In particular the source
V_K*g_K*f changes with K; the above-cutoff theorem does not assert
K >= modeCutoff(V_K*g_K*f).

A proposed next scalar lemma, NOT proved by this increment: for
0 <= w <= 1 and a_K(d)=w^(d(d+2)) when d<=K, zero otherwise,

    1 - a_K(d) <= (1-w)*d(d+2)

for every d, provided 1 <= (1-w)*(K+1)*(K+3). Below cutoff this is
the elementary power estimate; above cutoff the right side pays for
the omitted mode. This would avoid requiring the source degree to lie
below K. Turning it into a bare kinetic quadratic-form bound still
requires the actual norm/orthogonality identities, and turning that
into an ORIGINAL weighted bound still requires the signed endpoint
comparison. Neither consequence is claimed here.

No SAME-variance small rate, trajectory-uniform weighted estimate,
spatial/scaling survival, physical mass calibration, canonical full
OS/QFT or every-group realization follows from this finite expansion.
Inactive kinetic slots remain Haar projections. No canonical field,
analytic premise, hole or axiom was introduced, removed or weakened.

## Verification and division of work

Five focused checks passed 54 printed gates (16 radial, 9 recursion,
9 splitting, 16 arbitrary-input expansion, 4 original product consumer),
all within `{propext, Quot.sound}`. The dependency-complete target
`+YMGap.Continuum.SU2QuaternionProductHeatHarmonicExpansion:olean`
passed. Final focused logs contain no errors, warnings, `sorryAx` or
classical dependencies. The safe-build skill kept actual compilation
serialized with one capped 20 GiB worker. No full-root build, full-tree
audit or guard was run. Automatic CI remains manual-only.

Final logs:

- `/tmp/ym-gap-fischer-radial-check.log`
- `/tmp/ym-gap-fischer-decomposition-check.log`
- `/tmp/ym-gap-head-homogeneous-check.log`
- `/tmp/ym-gap-polynomial-harmonic-expansion-check.log`
- `/tmp/ym-gap-product-heat-harmonic-expansion-check.log`
- `/tmp/ym-gap-product-heat-harmonic-expansion-build.log`

Sol drafted the bounded exact-degree splitter and original product-map
consumer and independently reviewed the radial/Fischer argument (PASS).
Main constructed the radial identity, terminating decomposition, arbitrary-
input Haar/heat join, fixed-input cutoff, integration fixes and serialized
verification. Main also reviewed the product consumer's retained-factor
and support conditions.
Sol's final independent review of the arbitrary-input carrier/heat join
and fixed-input cutoff also passed. Its next-input inventory identified
the existing cross-degree cancellation above and the need to retain
equal-degree cross terms.
