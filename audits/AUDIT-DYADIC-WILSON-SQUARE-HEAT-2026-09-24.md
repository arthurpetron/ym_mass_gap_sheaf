# Original growing-word square heat and complete signed terminal formula

Date: 2026-09-24 UTC. Scope: exact finite original-Haar SU(2) identities,
arbitrary distinct-link ordered words, and the actual growing-square terminal
source. The constructive continuum Yang--Mills and physical mass-gap target
for every compact simple gauge group remains OPEN.

## Mathematical increment

For the original selected product heat P and a word with distinct selected
block indices, at every rational w and cutoff K>=2:

    P(chi_2(word)) = w^(8*perimeter) * chi_2(word),
    P(chi_1(word)^2) = 1 + w^(8*perimeter) * chi_2(word).

These are `SupportedHaarEqv` identities: they retain EVERY supported final
test in the original Haar functional. They are not literal polynomial
equalities and do not assert P is multiplicative. The square identity uses
the existing coefficient identity chi_1^2=1+chi_2 and constant preservation.

The one-link quadratic calculation retains its trace term:

    H[heat * scalar(x_a*p)^2 * r]
      = w^8 * H[scalar(x_b*p)^2*r]
        + (1-w^8)/4 * H[norm(p)*r].

The norm on the right is the ACTUAL polynomial norm. It is replaced by one
only under the original arbitrary-insertion Haar-unit relation. Source-block
independence and support are explicit; the tail and spectator may otherwise
depend on each other and the target block. Reversed links are handled by a
coefficient-level scalar conjugation identity, not by commuting quaternion
factors. The word induction retains the upper prefix, its coefficient-padded
lower pin, all remaining heat factors, and the full supported final test.
All unit/support/independence premises are derived for the actual word.

For the literal padded dyadic square, L=2^scale, let f be its original
fundamental character and q an arbitrary supported source. With

    a = w^(12*L), b = w^(32*L),
    M = H[q*q*f*f], N = H[q*q],

the full square image gives

    H[q*q*P(f*f)] = b*M+(1-b)*N.

For the ORIGINAL terminal message g and COMPLETE projected endpoint source
q=projectedEndpointSource(w,K,width,g), the existing signed-energy consumer
therefore yields

    4*energy(g,f) + sourceIncrementCost(q,f)
      = 2*((1-2*a+b)*M+(1-b)*N).

The signed coefficient, source increment correction, and both original
source moments remain. No positivity of a truncated kernel is asserted by
these identities at arbitrary rational w.

## Declaration evidence

| Declaration | Source | Content |
|---|---|---|
| `SU2QuaternionSelectedPairQuadraticHeat.coordinatePair_transmission_same_carrier` | `lean/YMGap/Continuum/SU2QuaternionSelectedPairQuadraticHeat.lean:85` | Full-carrier trace and trace-free quadratic channels. |
| `SU2QuaternionSelectedPairQuadraticHeat.coordinatePair_selected_transmission` | `lean/YMGap/Continuum/SU2QuaternionSelectedPairQuadraticHeat.lean:108` | Arbitrary distinct selected source/target blocks, original supported spectator. |
| `SU2QuaternionSelectedLinearHeatProduct.linearAt` | `lean/YMGap/Continuum/SU2QuaternionSelectedLinearHeatProduct.lean:36` | Explicit finite coordinate-linear polynomial. |
| `SU2QuaternionSelectedLinearHeatProduct.linear_product_transmission` | `lean/YMGap/Continuum/SU2QuaternionSelectedLinearHeatProduct.lean:260` | Complete coefficient Gram trace, with source independence only. |
| `SU2QuaternionIndependentTailHeat.scalar_square_transmission` | `lean/YMGap/Continuum/SU2QuaternionIndependentTailHeat.lean:125` | Exact tail norm retained in the quadratic trace channel. |
| `SU2QuaternionIndependentTailHeat.spinTwo_transmission` | `lean/YMGap/Continuum/SU2QuaternionIndependentTailHeat.lean:244` | Actual Haar-unit tail gives pure label-two factor w^8. |
| `SU2QuaternionSpinTwoWordStep.spinTwo_word_step` | `lean/YMGap/Continuum/SU2QuaternionSpinTwoWordStep.lean:89` | Both orientations inside an ordered prefix/letter/tail. |
| `SU2QuaternionProductHeatWilsonSpinTwo.pairing_with_prefix` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonSpinTwo.lean:138` | Prefix-pinned induction retains remaining kernels and final tests. |
| `SU2QuaternionProductHeatWilsonSpinTwo.productMap_spinTwo_word` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonSpinTwo.lean:242` | Original arbitrary-word multiplier w^(8*perimeter). |
| `SU2QuaternionProductHeatWilsonSpinTwo.productMap_fundamental_square` | `lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonSpinTwo.lean:263` | Full fundamental square image, including its vacuum channel. |
| `BF4DyadicWilsonSquareQuadraticHeat.paddedSquare_square_fullRange` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareQuadraticHeat.lean:83` | Actual square with b=w^(32*side); physical lookup and distinctness derived. |
| `BF4DyadicWilsonSquareQuadraticHeat.paddedSquare_square_moment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareQuadraticHeat.lean:120` | Complete arbitrary supported q retained in b*M+(1-b)*N. |
| `BF4DyadicWilsonSquareQuadraticHeat.paddedSquare_terminal_quadratic_identity` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareQuadraticHeat.lean:178` | Actual terminal message, projected source and signed energy/correction. |

The last theorem consumes
`BF4DyadicWilsonSquareSignedCost.paddedSquare_terminal_young_identity`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedCost.lean:86`.
Its original remaining square-image term is now evaluated, not assumed.

## Remaining causal work

The next A03 input is a useful comparison of this complete signed expression
with the SAME interacting centered variance along a justified scaling family,
or a direct response lower bound on that family. N is H[q*q] for the actual
projected source; it is not silently identified with a physical partition or
centered norm. This milestone proves identities, not that quantitative join.

Bare P is not the interacting transfer P(V*f) or its completed temporal
operator. There is no new completed relative-loss/scaling estimate, continuum
survival, cross-width state identification, EVERY-state physical rate,
thermodynamic/continuum modulus, full QFT/YM/UV construction, physical
Hamiltonian/mass identification, or all-group result here.

## Verification and chart delta

Six final serialized narrow checks exited zero. Nineteen printed gates are
within {propext, Quot.sound}: thirteen public gates, including one axiom-free
definition, and six private-helper diagnostic gates. The launcher was
`scripts/safe_lean_build.py --jobs 1 --check <leaf> --check-output <olean>`
with `--check-worker-limit-gib 2`, default elaboration limits, and the unchanged
12 GiB OS reserve. No thresholds were raised. No full-root/full-tree build,
axiom audit, guard or progress suite was run.

Initial failed drafts are not accepted evidence. In particular, diagnostic
gates isolated `Classical.choice` in a dependent finite-index match; replacing
it with the existing constructive coefficient-case pattern removed that
dependency. Local character and scalar regrouping lemmas also avoided
unnecessary unfolding at the default heartbeat limit. No source hole,
new axiom, analytic premise, or canonical-field change was introduced.
Independent final source/scope review found no mathematical blocker and
confirmed the final sixth-leaf gate log after its earlier failed attempt.

| Final local log | Gates | SHA-256 |
|---|---:|---|
| `/tmp/ym-gap-selected-pair-quadratic-check-2.log` | 2 | `74faea6e628ab8de2f1cd8bc97b02c9fb2a898e71b7746568e630252c5f675d1` |
| `/tmp/ym-gap-selected-linear-heat-check-2.log` | 2 | `0cb5208b276f68ad757cb4890943521d66de06ce1f0546581db42fbbdcd420f8` |
| `/tmp/ym-gap-independent-tail-heat-check-4.log` | 8 | `fe22e59b2c8d01e53c8074bcc5e1fb0b04646fbdf1a56be2dfbe5aa34bf00369` |
| `/tmp/ym-gap-spin-two-word-step-check-3.log` | 1 | `b331f1fb952227a75b142043d0d4ee83de94ac6bb6803cc8af674687037573ed` |
| `/tmp/ym-gap-product-heat-wilson-spin-two-check-3.log` | 3 | `b7e8c3406bca1d5573eec3c4a58f3d27de1dddbb89df6a7d8c5f86db3904bf58` |
| `/tmp/ym-gap-dyadic-square-quadratic-heat-check-2.log` | 3 | `c09fb21929476fff20e4937cebf8b7fe2258ebbe0a91578e2d9178265ef7deee` |

Logs are local verification evidence, not tracked artifacts. The semantic
root imports the stronger terminal consumer in place of its predecessor;
the predecessor remains imported transitively. Schema 1 snapshot 19 adds
partial A03 evidence only. The exact chart block, labels, layout, symbols,
registered scopes and every goal-node marker are unchanged.
