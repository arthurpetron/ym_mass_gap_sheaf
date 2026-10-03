# The SAME original dyadic derivative and regularized series coincide

The whole-project goal remains nontrivial continuum Yang--Mills on R^4 for
every compact simple group, with SAME-theory QFT axioms and a positive
physical Hamiltonian mass gap. It is OPEN. This increment identifies BOTH
EXISTING bounded positive-time maps, not a full-carrier physical Hamiltonian,
canonical continuum OS theory, or changing-family scaling estimate.

## Actual forward/backward meeting point

`lean/YMGap/Continuum/BF4WilsonAllNomeRootLogIdentification.lean:215`,
`derivativeAction_eq_regularizedLog`, proves for every original completed
state, width and 0<w<1:

    derivativeAction hw0 hw1 x = regularizedLog hw0 hw1 x.

Both maps are the EXISTING constructions: `BF4WilsonAllNomeDyadicDerivative.lean:274`,
`derivativeAction`, and `BF4WilsonAllNomeLogSeries.lean:167`, `regularizedLog`
(same source directory). No replacement carrier, time action, limit object,
Cauchy rows, operator inverse or boundary-kernel exclusion is introduced.

## Explicit quantitative construction

`RootLogIdentification.lean:128`, `harmonic_scaled_norm_small`, uses the
SAME supplied Cauchy representative's computed norm ceiling and tolerance
denominator. `rangeModulus` is that denominator, not an implicit logarithmic
threshold. :151, `finite_comparison_small`, consumes the proved ACTUAL norm
comparison and constructive rational inequality

    (2*h+v)^2 <= 8*h+2*v, 0<=h,v<=1,
    h=half^d, v=invSucc(M).

Root and log cutoffs are independent, but both use ONE original representative.
:178, `identificationRate`, computes

    rangeModulus X (quarter (quarter (quarter epsilon))) + 2.

:183, `quotient_to_log_bound`, proves every later ORIGINAL quotient is
within epsilon in the actual squared distance of EXISTING regularizedLog.
Its finite comparison chooses the positive log cutoff

    M=max 1 (max (convergenceModulus X (quarter epsilon))
                (rangeModulus X (quarter (quarter epsilon)))).

The original log approximation and actual distance triangle then meet the
EXISTING `BF4WilsonAllNomeCauchyRows.lean:74`, `limit_unique`, on the
EXISTING quotientRows. Quotient induction proves map equality without
choosing representatives of arbitrary quotient-valued sequences.
The preceding finite norm evidence is retained in
`audits/AUDIT-ORIGINAL-ROOT-LOG-NORM-COMPARISON-2026-10-03.md`.

## Scope and repointed mathematical frontier

The map differentiates the positive-time image T(1)x. Equality does NOT
assert that T(1) is injective or that a whole-carrier physical Hamiltonian
has been constructed. The original counterexample to such injectivity
remains `BF4WilsonAllNomeFringeTimeKernel.lean:94`,
`completedTime_one_not_injective_width_one` (same source directory).

The next substantive target is the ORIGINAL combined signed cost relative
to SAME OWN variance, or a retained macroscopic response ratio, on a
JUSTIFIED changing family. `BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`,
`dyadicUnitResponse_filtered_block_floor`, still takes `hbudget` as an
explicit assumption; this identification does not produce it. The complete
signed multiplication component is checked nonpositive at fixed parameters
in `BF4WilsonAllNomeSignedMultiplicationLimit.lean:132`,
`signedCostLimit_nonpositive`, not a bound for the other combined terms.

`CanonicalOSRoot.lean:268`, `PositiveTimeOSRoot`, still specifies the
required canonical reflected positive-time realization. The fixed-carrier
map equality does not inhabit it for a continuum theory. Continuum survival,
physical calibration, full QFT, every-group construction and Clay remain OPEN.
No new fixed-carrier gap wrapper replaces these unpaid analytic inputs.

## Focused verification boundary

One NEW target passed the focused b-check, reporting five gates, all within
{propext, Quot.sound}. Root reviewed the complete source; Sol supplied the
explicit limit join. Review is not proof. The accepted log exited zero with
no error, warning, sorryAx or PANIC.

The a-log exposed integer-only reflector constants and a default elaboration
heartbeat limit in the generic distance-data application. The accepted b-proof
uses a symbolic half plus closed rational coefficient cancellation and a
specialized proof from the ACTUAL distance triangle. No heartbeat, memory,
axiom, statement or hypothesis was changed; no resource cap was raised.

The monitored launcher used one worker, 20-GiB cap, 12-GiB reserve, after
fresh memory/process/swap checks: 84% free memory and zero swap. No concurrent
build, full root/tree build, broad audit/guard or progress metric ran.
Root import registered only. No sorry, axiom, frontier weakening, CI or
exact canonical chart change.

| Artifact | SHA-256 |
| --- | --- |
| lean/YMGap/Continuum/BF4WilsonAllNomeRootLogIdentification.lean | 5d0c702e9b56411b89f2d8e5349cfe6eed62c5bb08f72b9b923bbc7af7164bed |
| /tmp/ym-original-root-log-identification-20261003-b.log | f4318b295145c614b8973f0002ef0a93742a25dd1bb565b76b67748e960fb26e |

Canonical first-chart SHA-256 remains
`0d9295165945a8acea2c4037bd951f9060a1dfcc22448bde4462d0c795b12145`.
