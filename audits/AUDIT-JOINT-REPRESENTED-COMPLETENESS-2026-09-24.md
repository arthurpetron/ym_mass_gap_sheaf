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
