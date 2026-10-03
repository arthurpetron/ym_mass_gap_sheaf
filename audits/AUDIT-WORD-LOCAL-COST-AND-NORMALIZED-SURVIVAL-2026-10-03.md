# Word local cost and normalized survival

Subsequent support result: conditional normalized continuity is checked in
`audits/AUDIT-NORMALIZED-ANCHOR-CONTINUITY-2026-10-03.md`. The original
31-gate checkpoint and remaining-input snapshot are preserved below.

Two constructive results reduce the forward and backward requirements without
producing the missing scaling-family estimate. The actual Wilson-square gain
now costs only its word-local conditional source fluctuation. Independently,
a normalized positive-time excitation has a positive blocked response floor
from a relative budget, without a uniform raw-norm reserve. Both results use
the original SU(2) objects. The continuum Yang--Mills and Clay targets remain OPEN.

## Forward estimate retains the original action

`localSourceResidual`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatWilsonLocalCovariance.lean:222`,
is q-QS, where QS=hybridSweep(selected,q). It integrates only the selected
lower word slots. All other lower coordinates and all upper coordinates
remain. `localSourceLoss` at line 227 is the square of that residual under
W=the FULL original product heat times the lifted original upper weight R.
It is not an observable's OWN variance.

`localSourceResidual_orthogonal` at line 337 proves orthogonality to every
supported doubled test independent of the selected lower slots, under that
SAME W. Independence is required of the test, not the source. The proof
uses the original conditional heat normalization; it is not ordinary Haar
orthogonality or a deletion of the action factors.

`localSourceLoss_pythagoras` at line 352 proves the exact identity

    fullSourceLoss = localSourceLoss
      + B_W(QS-lift(Pfull q), QS-lift(Pfull q)).

Here fullSourceLoss denotes its retained upper integral. The second term
is a literal square under the SAME W. With the original heat and R
certificates, `localSourceLoss_nonnegative` at line 407 and
`localSourceLoss_le_fullSourceLoss` at line 419 prove

    0 <= localSourceLoss <= fullSourceLoss.

`fundamental_word_local_covariance_pair_retained_bound` at line 801 proves,
for the same scalar ordered word f and P=its perimeter,

    H[R*b*(Pfull(q*f)-a*(Pfull q)*f)]^2
      <= localSourceLoss * [(1-d)*H[R*b^2]-(a^2-d)*H[R*b^2*f^2]],
    a=w^(3*P), d=w^(8*P).

The guards retain 0<w<1, K>=headCutoff(w), K>=2, supported source/test/weight,
an actual R certificate, distinct active heat indices, and distinct selected
mapped word indices. All kinetic and spectator factors remain. The signed
spin-two subtraction is retained rather than capped away.

## Actual growing square consumer

`originalLocalSourceHeatLoss`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainLocalCovariance.lean:67`,
uses q=V*g_n, R=V, the full original active heat kernel and ONLY the
padded square's lower word slots as selected slots. Here V is the original
spatial action and g_n the original terminal message.

`originalLocalSourceHeatLoss_le_full` at line 100 proves domination by the
previous actual full-source cost. `paddedSquare_fullSourceDefectPair_local_retained_bound`
at line 122 proves the actual geometry, activity, distinctness and source
recoding before specializing the new bound. No geometric recoding input
is assumed.

`paddedSquare_own_commutatorGain_local_retained_bound` at line 218 uses the
actual finite OWN odd mean c, b=T(g_n*(f-c)), A=Tg_n, and proves

    [G2-(a-1)*c*ell(A*b)]^2
      <= originalLocalSourceHeatLoss
        * [(1-d)*ell(b^2)-(a^2-d)*ell(b^2*f^2)],
    a=w^(12*side), d=w^(32*side).

This is a smaller proved source cost for the SAME original gain, not a
gain sign or a comparison with interacting variance. The mean correction
is still literal. Its existing geometric payment is
`own_meanResidue_tolerance_bound`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredMeanResidueBound.lean:241`.
That modulus is parameter-dependent, not a uniform changing-family onset.

## Backward survival no longer needs a uniform raw reserve

`anchorNorm`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedBondAnchor.lean:61`,
is N=R(2*side) on the existing unit state u and completed time action.
`anchorNorm_floor` at line 72 retains the already-proved, positive,
parameter-dependent floor. `anchorNormalizer` at line 76 constructs its
inverse square root with explicit Cauchy data; no uniform lower bound on N
is assumed.

`normalizedSector` at line 102 retains the original range witness.
`normalizedBondExcitation` at line 107 is its image in the EXISTING physical
bond completion. `normalizedVacuumExcitation` at line 111 retains the
original vacuum-complement proof. The vector is the explicitly constructed
z=N^(-1/2)*T(side)*u, NOT literally u. `normalizedBond_value` at line 124
identifies the two realizations, and `normalizedVacuumExcitation_norm` at
line 147 and `normalizedBond_norm` at line 155 prove norm exactly one.

`normalizedAnchorResponse_cleared_pin` at line 161 proves

    N*Rz(j) = R(2*side+j)

as CReal.Equiv, on the SAME carrier and time action. It does not assume a
CReal division operation or a cross-scale identification.

`normalizedAnchorResponse_budget_geometric_floor` at line 223 consumes the
ORIGINAL budget m*(R(start)-R(start+1))<=C*R(start), with start<=2*side,
C>=1 and m>=4*C, and proves Rz(j)>=blocked_rate(C,m)^j.
`normalizedAnchorResponse_budget_block_floor` at line 284 proves

    Rz(m-1) >= (1/4)^(2*C).

Thus a fixed family-wide C would give a fixed positive floor without a
uniform raw R1 or N reserve. The actual budget is still unsupplied. The
earlier unanchored criterion retains its explicit raw R1 reserve; it is an
alternative, not a necessary prerequisite for this normalized route.

## Remaining mathematical join

The forward estimate must control the retained local source cost and signed
character moment relative to the SAME completed response, or establish a
suitable signed gain directly, on an explicitly justified scaling family.
The new local loss is not identified with OWN variance, nor is its useful
relative size proved. No favorable gain sign is inferred from a squared bound.

Normalized time continuity without dividing an absolute modulus by collapsing
N is the next backward support task. Cross-scale convergence, nontrivial
continuum survival, original local-field identification, physical calibration,
uniform EVERY-state decay, full same-theory QFT structure and every compact
simple group remain OPEN. No canonical displayed claim changed.

## Focused verification

The three frozen targets passed 31 printed constructive gates, respectively
7, 4 and 20. Every dependency set is contained in {propext, Quot.sound}.
Independent source/log QA and mathematical review checked the same objects
and scopes. No sorry, new axiom, classical shortcut or field weakening was
introduced. Imports are registered, NOT aggregate-checked; no full build,
audit or guard run is claimed. CI and the canonical chart fence are unchanged.

Each check used scripts/safe_lean_build.py, one worker, an explicit 20-GiB
worker cap and a 12-GiB system reserve. Fresh preflights showed no competing
compiler, at least 85% memory-pressure-free and no swap. The actual consumer
uses a theorem-local heartbeat budget of 1000000 for one private algebraic
helper; global options and memory ceilings are unchanged.

| Source | Accepted log | Gates |
| --- | --- | --- |
| SU2QuaternionProductHeatWilsonLocalCovariance.lean | /tmp/ym-word-local-covariance-20261003-sixth.log | 7 |
| BF4DyadicWilsonSquareFilteredGainLocalCovariance.lean | /tmp/ym-square-local-covariance-20261003-fourth.log | 4 |
| BF4WilsonAllNomeDyadicNormalizedBondAnchor.lean | /tmp/ym-normalized-bond-anchor-20261003-second.log | 20 |

SHA256 source/log pairs in the same order:

    591a1f81bfdb2be0747a8e2029ed0b3d99f6fc16decaaaaf84a4db1ef9c7673d
    a6a75c85afe4d47575bb63c908f49703133edb26f59e00908c9481bb06041c7b
    3b4cb950b7e82e7d0f5d989b7060a4b1826466ffc62a5947e2e2915e20bb2357
    a59d2c2e6c9da54a51fa5c1efe7e1b79d5188d2aea372e1a825e4de75e7da363
    c706d730448e458eacbacf207ff81365fb68d26819ca05c02a4d69b044f7e479
    dde10e9d170b688d3a25a773ff375105a57b39714a8def532b984151eaeed7f6

Earlier failed drafts and their axiom output are not proof evidence.
