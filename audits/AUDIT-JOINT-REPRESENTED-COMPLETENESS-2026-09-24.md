# Represented norm completeness on the SAME reflected carrier

Date: 2026-09-24 UTC. The continuum Yang--Mills/Clay target remains open.

## Mathematical result

Fix the original rational nome `0 < w < 1` and spatial width. Let `B` be
`BF4ExactSlabFixedSpatialJointCompletedInner.completedInner` on the existing
`JointCompletion`. Supply `pt : Nat -> D.Cauchy` and a modulus for

    B(pt_p - pt_q, pt_p - pt_q) <= epsilon

when both outer indices clear the modulus (points in this formula denote
the quotient classes of the supplied representatives). The new construction
returns a point L of this SAME carrier and a rate `limitRate` such that

    B(pt_p - L, pt_p - L) <= epsilon

for every p beyond the displayed rate. It does not assume the stronger
eventual comparison of representatives: `late_distSq_le` derives that
comparison from the actual completed norm and existing explicit pairing rate.

The generic diagonal uses three comparisons and the squared triangle law,
with a ten-copy rational budget. General outer moduli are constructively
reindexed. All indices remain functions/data; no quotient representative
is selected and no modulus is extracted from an erased existence proof.

## Declarations and actual consumer

- `lean/YMGap/Continuum/CRealSeminormPresentedCompleteness.lean`:
  `GeneralPresentedCauchy.diagonal`, `convergesToDiagonal`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPresentedCompleteness.lean`:
  `late_distSq_le`, `PresentedNormCauchy.toPresented`, `limit`,
  `limitRate`, `limit_converges`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointPresentedLimitLaws.lean`:
  `CandidateLimit.closeDiagonal`, `eq_constructed_limit`,
  `PresentedNormCauchy.mapTime_limit`.

Uniqueness follows by comparing two candidate representatives through a
common late outer point, with an explicit closeness modulus. The time map
acts on supplied representatives by its existing nonexpansive construction.
Uniqueness identifies the time image of L with the constructed limit of the
time-mapped family. Thus the result is compatible with the actual transfer,
not only an abstract completion interface.

The next consumer at this checkpoint was `JointRangeApproximation.evenOrbitSum`. Its checked
residual error tends to zero, but the approximating vectors still need their
own Cauchy estimate before completeness supplies an exact inverse image.
That estimate and exact inverse are now proved in the subsequent
[Neumann-inverse checkpoint](AUDIT-JOINT-NEUMANN-INVERSE-2026-09-24.md).

## Boundary and verification

This is represented completeness, not a lift of arbitrary quotient-valued
sequences. It constructs neither the full Hilbert/OS/QFT package nor continuous
time/a Hamiltonian. It adds no spatial or spacing uniformity, continuum
nontriviality, physical mass bound, or all-group construction.

Three serialized leaf checks used `scripts/safe_lean_build.py`, one worker
and a 4 GiB cap. Accepted logs:

- `/tmp/ym-gap-presented-completeness-check-2.log`: ten gates, only `propext`.
- `/tmp/ym-gap-joint-presented-completeness-check-4.log`: eight gates,
  only `propext` and `Quot.sound`.
- `/tmp/ym-gap-joint-presented-limit-laws-check-2.log`: five gates,
  only `propext` and `Quot.sound`.

All three exited successfully. No error, warning or `sorryAx` occurs in the
accepted logs. Semantic-root import added; no full-root build, audit or guard
was run. No hole, new axiom or canonical-frontier statement change was made.

## Complex limits and matrix-coefficient consumer

Follow-up, 2026-09-24 UTC. On the existing `ComplexCarrier`, not a replacement
GNS model, complex squared distance is exactly the sum of the two real squared
distances. Nonnegativity bounds each component by this sum. The supplied
complex Cauchy data therefore produce two real represented Cauchy families;
their limits and half-error moduli construct the complex limit. Candidate
uniqueness and the existing real transfer-limit laws prove complex time
compatibility.

New declarations:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexPresentedCompleteness.lean`:
  `PresentedComplexCauchy.limit`, `limitRate`, `limit_converges`,
  `CandidateLimit.eq_constructed_limit`, `PresentedComplexCauchy.mapTime_limit`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointComplexPairingContinuity.lean`:
  `inner_two_bound`, `pairing_error_bound`, `testNormCap`, `pairingRate`,
  `pairing_converges`, `time_pairing_converges`.

The actual consumer uses the explicit bound

    |<x-y,test>|^2 <= 2 * ||x-y||^2 * ||test||^2.

This is a continuity estimate, NOT sharp complex Cauchy--Schwarz. Four sharp
real inequalities and the two-term square bound prove it; all complex cross
terms are retained until that inequality. The original strict transfer rate
is unchanged. From supplied test representatives, `testNormCap` computes a
positive rational ceiling C. Applying norm convergence at `(epsilon/2)/C`
proves squared pairing error at most epsilon. The time consumer applies this
to the actual time-mapped family and uses the proved same-transfer limit
identity. Time is fixed in this statement; no time/scaling uniformity is
asserted. No new completeness or analytic assumption is supplied.

Accepted serialized one-worker 4 GiB logs:

- `/tmp/ym-gap-joint-complex-completeness-check-2.log`: twelve gates.
- `/tmp/ym-gap-joint-complex-pairing-continuity-check-3.log`: ten gates.

Both checks exited zero, with only {propext, Quot.sound} and no error,
warning or sorryAx in the accepted logs. The independent source review
confirmed the supplied representatives, actual norm and half-error modulus.
Semantic consumer import added; no full-root build/audit/guard was run.

These are fixed-nome/fixed-width represented Hilbert prerequisites, not full
Hilbert/OS/QFT or continuous Hamiltonian construction. The changing-scale
SAME temporal-energy/variance producer, separate EVERY-vector gap scaling,
continuum survival, physical mass, local YM fields and all groups remain open.
