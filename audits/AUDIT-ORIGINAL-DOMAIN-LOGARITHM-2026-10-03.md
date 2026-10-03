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
| `regularizedLog_tail_norm_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:87` | Existing regularized-log limit preserves the core-tail bound. |
| `graph_logarithm_tail_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:138` | Existing graph limit preserves the bound without uniform preimage caps. |
| `domainLogModulus` | `BF4WilsonAllNomeDomainLogarithm.lean:170` | Computed rate from p.output.range. |
| `domainLogarithm_bound` | `BF4WilsonAllNomeDomainLogarithm.lean:175` | Ordinary log partials converge to the SAME domain action. |
| `domainLogarithmCertificate` | `BF4WilsonAllNomeDomainLogarithm.lean:183` | Action and convergence modulus returned as data. |

The joins use existing `BF4WilsonAllNomeNormLimitOrder.norm_limit_order`
at `lean/YMGap/Continuum/BF4WilsonAllNomeNormLimitOrder.lean:96` and
`derivativeAction_eq_regularizedLog` at
`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogIdentification.lean:215`.
Decay uses `defect_small` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeClosure.lean:101`.

## Focused verification boundary

Three serialized safe-launcher checks passed with one worker, mandatory
20 GiB ceiling and 12 GiB OS reserve. Fresh preflight showed 83--84% memory
free, no competing compiler/runner and zero swap. Accepted logs report 18
gates, all within {propext, Quot.sound}, with no error, warning, sorryAx or PANIC.

| Target | Accepted log in /tmp | Gates |
|---|---|---|
| `BF4WilsonAllNomeLogTailComparison.lean` | `ym-original-log-tail-comparison-20261003-b.log` | 8 |
| `BF4WilsonAllNomeUnregularizedLogPartial.lean` | `ym-original-unregularized-log-partial-20261003-a.log` | 5 |
| `BF4WilsonAllNomeDomainLogarithm.lean` | `ym-original-domain-logarithm-20261003-b.log` | 5 |

Source SHA256, in table order:

    f58eab704170adb0a4f40119b9e36742b4bb38bbe02b6e1250da60a4d0df77d6
    ae5d2eb5fc5642c07962c62e0fc475487e747c5da16ab0df9dcabfc526bd2af3
    3315158e40669cbb2bb93982e22defd3f5dad54084c065f85d5271d1d73db6fb

Accepted-log SHA256, in table order:

    507def8979bca5fe9d379524831dd7e4b26d4e09b20edf9df0c854d006051d13
    e5442c06badc6b64c0690670d93e45f726a1f48e82720fe34874aaa752ae3409
    5197796963f1e71a1ca4ae815cd4c1ca54cea6949d27bfb82cc5f9dca35e389d

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
