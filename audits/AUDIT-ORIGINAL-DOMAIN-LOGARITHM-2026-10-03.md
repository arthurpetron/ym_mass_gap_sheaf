# Ordinary logarithm on the existing original derivative domain

The unchanged goal is a nontrivial continuum Yang--Mills theory on R^4 for
every compact simple group, SAME-theory QFT axioms and a finite positive
physical mass gap. It remains OPEN.

## New proved statement and its actual consumer

Put D=I-T for the EXISTING original all-nome Wilson transfer and define the
literal finite sum U_M x=sum_(j=1..M) D^j x/j. Every EXISTING
`SectorDerivative.DomainPoint` p now has

    dist(U_M p.input, p.output) <= ||D^M p.output||^2,
    dist(U_M p.input, p.output) <= epsilon
      whenever domainLogModulus(p,epsilon) <= M.

`dist` is the original squared distance. The modulus is the existing output-
range `defectModulus`, retaining its original preimages. The Type-valued
`domainLogarithmCertificate` returns the SAME action and this modulus.
No inverse transfer, spectral theorem or preimage norm cap is assumed.
The ambient fringe kernel is retained, not removed.

The converse is NOW also proved: `LogLimitPoint` supplies the SAME sector
input/output states and an ordinary-log convergence modulus; applying the
original transfer preserves that bound. The EXISTING regularized-log limit
uniqueness gives A input=T output and constructs `domainPointOfLogLimit`.
`logLimitPointOfDomain` computes the forward modulus without a new premise;
`domain_of_log_of_domain` returns the identical original domain point.
The reverse join need not preserve a supplied rate witness, and does not
claim equality of moduli. This is a data-valued domain characterization,
not an assertion that the series converges on every ambient vector.

This identifies the already constructed fixed-carrier domain action with
the ordinary transfer-log series. It is not an everywhere-defined ambient
logarithm, canonical physical OS realization, physically calibrated
Hamiltonian, or spatial/scaling-uniform estimate.

## Causal source anchors

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | File:line | Proved role |
|---|---|---|
| `filteredTail_pair_mono` | `BF4WilsonAllNomeLogTailComparison.lean:98` | Both sums retain positive actual mixed pairings; reciprocal coefficients are compared before the norm. |
| `logTail_norm_le_shifted_partial` | `BF4WilsonAllNomeLogTailComparison.lean:155` | Actual finite tail norm <= norm of D^M applied to the unshifted regularized partial. |
| `unregularizedLogPartial` | `BF4WilsonAllNomeUnregularizedLogPartial.lean:49` | Literal U_M without a time-one regularizer. |
| `unregularizedLogPartial_time` | `BF4WilsonAllNomeUnregularizedLogPartial.lean:54` | U_M(Tx) equals the existing logPartial_M x. |
| `unregularizedLogPartial_distance_bound` | `BF4WilsonAllNomeUnregularizedLogPartial.lean:105` | Computed M^2 fixed-cutoff continuity, including M=0. |
| `regularizedLog_tail_norm_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:97` | Existing regularized-log limit preserves the core-tail bound. |
| `graph_logarithm_tail_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:148` | Existing graph limit preserves the bound without uniform preimage caps. |
| `domainLogModulus` | `BF4WilsonAllNomeDomainLogarithm.lean:180` | Computed rate from p.output.range. |
| `domainLogarithm_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:185` | Ordinary log partials converge to the SAME domain action. |
| `domainLogarithmCertificate` | `BF4WilsonAllNomeDomainLogarithm.lean:193` | Action and convergence modulus returned as data. |
| `time_unregularizedLogPartial` | `BF4WilsonAllNomeDomainLogarithm.lean:201` | Original transfer commutes with each literal finite log. |
| `LogLimitPoint` | `BF4WilsonAllNomeDomainLogarithm.lean:214` | Ordinary-log domain retains both existing sector witnesses and a supplied modulus. |
| `logLimit_equation` | `BF4WilsonAllNomeDomainLogarithm.lean:224` | Contraction and existing limit uniqueness prove the original domain equation. |
| `domainPointOfLogLimit` | `BF4WilsonAllNomeDomainLogarithm.lean:237` | Constructs the original domain point without replacing its states. |
| `logLimitPointOfDomain` | `BF4WilsonAllNomeDomainLogarithm.lean:243` | Constructs the ordinary-log witness with a computed rate. |
| `domain_of_log_of_domain` | `BF4WilsonAllNomeDomainLogarithm.lean:250` | Forward/backward construction returns the identical original domain point. |

The joins use existing `BF4WilsonAllNomeNormLimitOrder.norm_limit_order`
at `lean/YMGap/Continuum/BF4WilsonAllNomeNormLimitOrder.lean:96` and
`derivativeAction_eq_regularizedLog` at
`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogIdentification.lean:215`.
Decay uses `defect_small` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosure.lean:101`.

## Focused verification boundary

Three targets passed serialized safe-launcher checks with one worker,
mandatory 20 GiB ceiling and 12 GiB OS reserve. The Domain target was rechecked
after the converse extension. Fresh preflight showed 83--84% memory free,
no competing compiler/runner and zero swap. Current accepted logs report 23
gates, all within {propext, Quot.sound}, with no error, warning, sorryAx or PANIC.
The initial forward checkpoint `bd95348` covered 18 gates; the converse adds
five gates, all accepted on its first focused check.

| Target | Accepted log in /tmp | Gates |
|---|---|---|
| `BF4WilsonAllNomeLogTailComparison.lean` | `ym-original-log-tail-comparison-20261003-b.log` | 8 |
| `BF4WilsonAllNomeUnregularizedLogPartial.lean` | `ym-original-unregularized-log-partial-20261003-a.log` | 5 |
| `BF4WilsonAllNomeDomainLogarithm.lean` | `ym-original-domain-logarithm-converse-20261003-a.log` | 10 |

Source SHA256, in table order:

    f58eab704170adb0a4f40119b9e36742b4bb38bbe02b6e1250da60a4d0df77d6
    ae5d2eb5fc5642c07962c62e0fc475487e747c5da16ab0df9dcabfc526bd2af3
    9f3527c629b042a7af2b58443be8ca5c2a3a3d073d4fc25ed0edff70ce0bbd64

Accepted-log SHA256, in table order:

    507def8979bca5fe9d379524831dd7e4b26d4e09b20edf9df0c854d006051d13
    e5442c06badc6b64c0690670d93e45f726a1f48e82720fe34874aaa752ae3409
    6436be5ccd06c414c7e909169c053265ce27b1d33f7186e71ca9487d1a0ac6a0

Earlier local failures were corrected namespace/scalar-orientation errors;
no resource or statement was weakened. No full-root/tree build, broad audit,
guard or progress metric ran. Semantic root imports are registration-only.
No sorry, axiom, classical shortcut or frontier weakening was introduced;
CI and exact chart remain unchanged.

## Forward frontier retained

The ORIGINAL combined signed cost versus SAME filtered OWN variance, or a
retained macro response ratio, on a JUSTIFIED family remains unpaid.
`audits/MATH-NOTE-CHANNEL-RELATIVE-FRONTIER-2026-10-03.md` records the
source-reviewed exact channel alternative and invalid bare-heat Perron
shortcut; that note is reasoning, not another checked estimate.
Canonical OS, continuum survival, physical calibration, QFT, every group
and Clay remain OPEN. No exact displayed chart claim changes.
