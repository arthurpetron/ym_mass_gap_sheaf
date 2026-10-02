# Positive scalar word alignment fails at cutoff two

## Result and proof path consequence

An explicit strictly positive scalar source defeats the proposed two-link
whole-word heat floor at nome 1/2 and retained cutoff 2. The source fits inside
that cutoff, and the elementary scalar one-link cutoff guard holds. This
rules out the unrestricted finite-cutoff whole-word claim, not the proved
one-link theorem, an adequately retained full-heat claim, or the original
four-dimensional Wilson estimate. No continuum or Clay obligation is closed.

## Actual source and kernel

For x=(a,b,c,d), y=(e,f,g,h), the five-monomial `source`
(`lean/YMGap/Continuum/SU2QuaternionScalarWordCutoffObstruction.lean:47`) is

    q = (a^2-b^2)*(e^2-f^2) + 4*a*b*e*f.

`source_supported` (same file, line 68) and `source_degree` (line 79) prove
two-link support and degree two in each block. `word` (line 53) is the ACTUAL
ordered Hamilton product x*y. `P` (line 61) uses the existing
`productMap 2 half 2 [0,1]`, integrating the lower coordinates and retaining
the upper coordinates. `pair_original` (line 88) pins `pair` (line 63) to the
original doubled-carrier product-kernel integral, with the SAME source on both
sides. `wordPair` (line 65) sums its four actual word-component pairings.

`scalar_cutoff_guard` (line 84) proves sufficientCutoff(1/2)<=2. This is the
guard from `product_alignment_no_error`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatExactAlignment.lean:59`), whose
retained cutoff is K+1. It is NOT the original action's `headCutoff` guard
(`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`).
The new source is not identified with a Wilson terminal message.

## Exact counterexamples

`source_norm` (new file, line 98) gives H[q^2]=1/18. `source_pair` (line 101)
gives 1/1179648. `source_word_outputs` (line 105) checks that every P(q*F_alpha)
has empty exact rational normal form; `source_word_pair` (line 119) is zero.
Consequently `scalar_alignment_defect` (line 124) gives

    wordPair(q) - (1/2)^6 * pair(q) = -1/75497472.

`scalar_alignment_fails` (line 132) proves the inequality is false. The
omitted word channels, rather than a change of source or normalization, are
the obstruction.

The stronger witness is `positiveSource` (line 144), s=1+q/50.
`positiveSource_supported` (line 146) proves support, and
`positiveSource_floor` (line 152) RETURNS an existing square certificate for
s-1/2 under arbitrary Haar insertions. The explicit signed-polynomial cap is
25, computed by `polynomialCap`
(`lean/YMGap/Continuum/QuaternionHaarSupportedPolynomialInterval.lean:237`);
`polynomialInterval` (same file, line 250) supplies the certificate.
`positiveSource_haar_mass` (new file, line 159) gives H[s]=1.

`positiveSource_pair` (line 161) and `positiveSource_word_pair` (line 202) give

    pair(s) = 1 + 1/2949120000,
    wordPair(s) = 1/64.

`positive_alignment_defect` (line 212) gives slack -1/188743680000, and
`positive_alignment_fails` (line 220) refutes the floor. Finally
`no_positive_scalar_word_alignment` (line 234) refutes the universal scalar
statement even when support, the strict positive certificate and normalized
Haar mass are supplied.

The calculation never claims P(1) is coefficientwise 1. Rational
canonicalization preserves the required Haar pairings; the positive-source
word calculation uses linearity and the checked zero outputs. Computation
runs in Lean's kernel, not through an external proof oracle.

## Verification boundary

The final focused check exited 0 without errors or warnings on 2026-10-02 UTC:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/SU2QuaternionScalarWordCutoffObstruction.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionScalarWordCutoffObstruction.olean --log-file /tmp/ym-scalar-word-cutoff-20261002-accepted.log
```

All eighteen printed gates are within {propext,Quot.sound}; the scalar cutoff
guard is axiom-free. Earlier failed checks are not proof evidence. No new
sorry, axiom, analytic premise, erased witness, raised resource limit or
weakened frontier field was introduced. Independent final source/log review
passed.

| Artifact | SHA256 |
| --- | --- |
| Lean source | `754a802b01a1b35670aec1d36287a3ad3bb7bfe147b7733b35af041ee5011ddc` |
| Accepted focused log | `09d44c638117912c090c4b999ec887ae69e9570b210f08e57e2144d81a749133` |

One 20 GiB-capped worker retained the 12 GiB OS reserve. Preflight found no
competing compiler/runner and zero swap. No full-root/tree/build/audit/guard
was run. One root import is added; CI and the canonical chart are unchanged.

## Remaining original estimate

The result is ONLY the displayed two-link finite-cutoff counterexample.
Higher-cutoff families and full-heat comparisons are not proved by this file.
Source-dependent retention or omitted-channel control must be established
before using the rejected bound. It cannot be inferred from source positivity
or from the scalar one-link theorem.

The live original consumer remains `paddedSquare_energy_projection_bound`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean:279`): bound
the COMPLETE signed debt minus retained gain relative to OWN variance on a
justified changing family. This estimate, physical calibration, nontrivial
continuum survival, full same-theory QFT and every compact simple group remain
OPEN. The original Yang--Mills route is not refuted by the new source.
