# Original growing-word heat transmission and signed terminal cost

Date: 2026-09-24 UTC. Scope: exact finite original-Haar identities for SU(2),
literal growing-square geometry, and their original terminal-energy consumer.
The whole-project constructive continuum Yang--Mills and physical mass-gap
target for every compact simple group remains OPEN.

## Proved mathematical increment

For a literal ordered word whose selected quaternion block indices are
distinct, the ORIGINAL selected product heat satisfies

    P(chi_1(word)) = w^(3*perimeter) * chi_1(word).

Equality here is `SupportedHaarEqv`: equality after multiplication by EVERY
supported final test and integration in the original Haar functional. It is
not literal polynomial equality and is not obtained by commuting quaternion
letters. The induction keeps an arbitrary lifted prefix, removes the current
lower block by exact fundamental heat propagation, and integrates every
remaining heat factor by the original upper marginal.

The geometric leaf proves distinct underlying positive links on all four
sides of every positive square; reverse traversal does not create repeated
links. Actual index lookup is injective on those physical carrier members.
Strict padding supplies active membership and hence independence of the
square character from the complementary fringe. No source factor is assumed
independent of its own variables.

For the actual padded dyadic square, let L=2^scale, f be its original
fundamental character, a=w^(12*L), P the full-range bare product heat, and
H the original fixed-slice Haar functional. For EVERY supported source q,

    H[(q*q*f)*P(f)] = a * H[q*q*f*f],
    J(q,f) = (1-2*a)*H[q*q*f*f] + H[q*q*P(f*f)].

For g equal to the actual terminal message and q the COMPLETE projected
endpoint source, the existing original-energy identity then yields

    4*energy(g,f) + sourceIncrementCost(q,f)
      = 2*((1-2*a)*H[q*q*f*f] + H[q*q*P(f*f)]).

The source correction is retained, not dropped. These identities hold for
arbitrary rational w and explicit K>=1; they assert no positivity of the
truncated heat at that cutoff. The multiplier depends explicitly on w and
perimeter; no beta-, width-, or spacing-uniform contraction is asserted.

## Declaration evidence

| Declaration | Source | Content |
|---|---|---|
| `SU2QuaternionProductHeatWilsonWord.wordAt` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:52` | Actual ordered coordinate/conjugate word with explicit block lookup. |
| `SU2QuaternionProductHeatWilsonWord.word_independent` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:74` | All four coordinates have degree zero in a block absent from the word. |
| `SU2QuaternionProductHeatWilsonWord.pairing_with_prefix` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:145` | Prefix-preserving exact transmission with arbitrary supported final test. |
| `SU2QuaternionProductHeatWilsonWord.productMap_word_scalar` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:211` | Original scalar-word supported-Haar image. |
| `SU2QuaternionProductHeatWilsonWord.productMap_fundamental_word` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonWord.lean:248` | Exact fundamental multiplier w^(3*perimeter). |
| `BF4DyadicWilsonSquareNodup.squareEdges_links_nodup` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareNodup.lean:162` | Four sides use distinct underlying links. |
| `BF4DyadicWilsonSquareNodup.paddedSquare_links_nodup` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareNodup.lean:230` | Literal padding preserves link distinctness. |
| `BF4DyadicWilsonSquareNodup.paddedSquare_indices_nodup` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareNodup.lean:238` | Actual fixed-slice indices are distinct. |
| `BF4DyadicWilsonSquareHeatImage.paddedSquare_fringe_independent` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:84` | Strict padding derives the original-energy independence premise. |
| `BF4DyadicWilsonSquareHeatImage.paddedSquare_fundamental_fullRange` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:101` | Literal original square image, multiplier w^(12*L). |
| `BF4DyadicWilsonSquareHeatImage.paddedSquare_fundamental_mixed_moment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareHeatImage.lean:138` | Full arbitrary supported source q retained in the mixed moment. |
| `BF4DyadicWilsonSquareSignedCost.paddedSquare_singleEndedCost` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedCost.lean:49` | Exact signed one-ended cost; actual square image remains literal. |
| `BF4DyadicWilsonSquareSignedCost.paddedSquare_terminal_young_identity` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedCost.lean:86` | ORIGINAL energy, terminal source, projection and correction in one identity. |

The last theorem consumes the already-proved
`BF4ExactSlabFixedSpatialSourceYoung.projected_young_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoung.lean:60`, and
`SU2QuaternionProductHeatSourceYoungMoments.singleEndedCost_eq_moments`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatSourceYoungMoments.lean:82`.
The new fringe lemma supplies the former's independence premise for the
growing square; the existing plaquette-only premise is not substituted.

## Remaining causal work

The actual arbitrary-growing-word square heat image P(f*f) has not been
evaluated here. The degree-one transmission cannot be squared: P is linear,
and no multiplicativity theorem is used or supplied. The four-link square
result `BF4ExactSlabFixedSpatialPlaquetteSquare.plaquetteSquare_fullRange`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSquare.lean:165`, is not
an arbitrary-word theorem.

The next signed-source calculation can evaluate that remaining image and
then must prove a useful comparison with the SAME interacting centered
variance along a justified scaling trajectory. The exact formula above
alone supplies no such estimate. Stronger direct-response alternatives
remain admissible; completing a particular scaffold is not the objective.

Bare P is NOT the interacting map P(V*f) or the completed physical transfer.
No new relative-loss estimate, scaling-survival assertion, cross-width
state map, universal physical rate, continuum limit, full QFT/YM/UV theorem,
Hamiltonian/mass identification or all-group construction is proved.

## Verification and stable-chart delta

Four final serialized narrow checks exited zero with thirteen printed gates
inside {propext, Quot.sound}; `wordAt` has an empty axiom set. Commands used
`scripts/safe_lean_build.py --jobs 1 --check <leaf> --check-output <olean>`
with `--check-worker-limit-gib 2`, default elaboration limits and the
unchanged 12 GiB reserve. Earlier elaboration failures were corrected before
acceptance; they are not counted as successful checks. No safety threshold
was raised. Independent mathematical/source-scope review found no blocker.

| Local final log | Gates | SHA-256 |
|---|---:|---|
| `/tmp/ym-gap-product-heat-wilson-word-finalcheck.log` | 5 | `a8a9082e5cca5b335a64a207047bd018f0712dc8795eea59b0218ff5c4c53002` |
| `/tmp/ym-gap-dyadic-square-nodup-check-3.log` | 3 | `4530bc8f90bca764435e9baa04d72cfabd66e207fed764c103e52699d3663272` |
| `/tmp/ym-gap-dyadic-square-heat-image-check-3.log` | 3 | `a4c3af1c6faa5fa7c0fd2379a1af00cc938112670b855b8266e8afc272b11525` |
| `/tmp/ym-gap-dyadic-square-signed-cost-check-1.log` | 2 | `938cd839cdbae48901df0d93de399c3c314c3ee15b9624531ba8d2942ea789d4` |

Logs are local evidence, not tracked artifacts. No new source hole, axiom,
analytic premise, canonical-field change or surrogate replacement. One
selective semantic-root import; full-root/full-tree build, axiom audit,
guard and progress suites NOT run. CI remains unchanged and off.

Schema 1 snapshot 18 records partial A03 evidence. Goal-node status changes:
NONE. Chart wording, layout, symbols, scope registry and frontier marker are
unchanged. The canonical fenced block retains SHA-256
`1201d45415516d6791135982068aba2bba935a0d972d25d931dee374e20df041`.
