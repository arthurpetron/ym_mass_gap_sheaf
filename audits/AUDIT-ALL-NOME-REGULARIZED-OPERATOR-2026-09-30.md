# Positive bounded regularized operator on the original Wilson carrier

Date: 2026-09-30 UTC. Four final focused Lean checks passed; no broad run.
Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with same-theory QFT axioms and a positive finite
physical mass gap. That goal remains OPEN.

## Actual mathematical increment

The previous checkpoint constructed

```
F x = limit_N sum_{k=1}^N (I-T)^k T x/k
```

on the ORIGINAL all-nome fixed-width Wilson completion. This checkpoint
proves properties of that SAME limit, with no additional analytic premise:

- `B(Fx,y) = B(x,Fy)` and `B(x,Fx) >= 0`;
- `B(Fx,Fx) <= B(x,x)` and `dist(Fx,Fy) <= dist(x,y)`;
- additivity and homogeneity for rational scalars and for constructive-real
  scalars carrying their own Cauchy moduli;
- every output is in the pre-existing complement of the normalized vacuum.

The norm coefficient 1 is inherited without loss from the finite sums;
optimality of that coefficient is NOT claimed. The distance is squared
norm, so nonexpansiveness supplies the identity tolerance. Nome and width
are explicit parameters: this is a within-carrier statement for every
rational 0<w<1 and width, not a map identifying different carriers.

## Short proof and constructive data

The actual completed Cauchy--Schwarz inequality and bilinearity give a
two-slot pairing tolerance. Applied to represented rows, the existing
computed norm ceilings and both row moduli give `pairingModulus`.
`row_pairing_bound` compares the finite pairings with the pairing of the
SAME constructed limits. It also passes an arbitrary completed-real
rowwise norm upper bound to the limit.

Every finite term has form `invSucc k * mixedMoment x 1 (k+1)` in its
quadratic pairing, so positivity is provided by the original time-defect
moments. Finite symmetry passes to the limit using constant rows made from
supplied representatives; these are not the different dense presentation
rows. The two comparison rates are synchronized by their maximum.

Once F is symmetric, linearity needs no separate limit-addition machinery:

```
B(F(x+y),z) = B(x+y,Fz) = B(Fx+Fy,z).
```

The original positive-definite pairing then identifies the vectors.
The same argument works for a supplied-modulus constructive-real scalar.
Subtraction compatibility and the norm cap give distance contraction.
Symmetry together with the already proved F(vacuum)=0 gives orthogonality
of every output. No quotient representative is selected and no spectral
theorem is used.

## Declaration evidence

Paths below are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
| --- | --- | --- |
| `pairing_close` | `BF4WilsonAllNomeCompletedPairingContinuity.lean:104` | Actual completed pairing with explicit two-slot tolerance. |
| `pairingModulus`, `row_pairing_bound` | `BF4WilsonAllNomeRowPairingLimit.lean:87`, `:94` | Quantitative passage through supplied represented rows. |
| `rowLimit_norm_bound` | `BF4WilsonAllNomeRowPairingLimit.lean:135` | Arbitrary RC norm upper bound retained at the limit. |
| `constantRows`, `limit_constantRows` | `BF4WilsonAllNomeRowPairingLimit.lean:146`, `:161` | Original supplied class recovered exactly. |
| `logPartial_symmetric`, `logPartial_nonnegative` | `BF4WilsonAllNomeLogPartialAlgebra.lean:120`, `:126` | Finite original-operator producers. |
| `pairing_limits_eq` | `BF4WilsonAllNomeLogOperator.lean:76` | Equal row pairings have equal limit pairings. |
| `regularizedLog_symmetric` | `BF4WilsonAllNomeLogOperator.lean:85` | Symmetry of the existing limit map. |
| `regularizedLog_norm_bound`, `regularizedLog_nonnegative` | `BF4WilsonAllNomeLogOperator.lean:101`, `:115` | Actual boundedness and positive quadratic form. |
| `regularizedLog_add`, `regularizedLog_smul`, `regularizedLog_realSmul` | `BF4WilsonAllNomeLogOperator.lean:134`, `:141`, `:149` | Rational and supplied-modulus real linearity. |
| `regularizedLog_dist_bound` | `BF4WilsonAllNomeLogOperator.lean:162` | Actual squared-distance contraction. |
| `regularizedLog_orthogonal`, `regularizedLogVacuum` | `BF4WilsonAllNomeLogOperator.lean:169`, `:174` | Same-carrier vacuum-complement output. |

## Scope and execution priority

This closes the norm/linearity/symmetry residue explicitly left by the
previous regularized-series checkpoint. The new pairing-limit machinery
has this concrete consumer; it is not an uninhabited operator specification.
The existing dense `BF4WilsonAllNomePairingContinuity.lean` is unchanged.
Legacy thermodynamic continuity proofs were mathematical templates only;
their different-carrier conclusions were not substituted for actual proofs.

F is not identified with a scalar logarithm, a physical Hamiltonian, or a
continuous-time generator. Its actual positive-norm boundary kernel is
still annihilated, not removed. Its norm bound does not imply decay of T
or a physical mass gap, for abelian or non-abelian groups.

Do not pursue full-carrier generator reconstruction by assuming away that
kernel. Return the main analytic effort to useful original-action signed
control on justified scaling and controlled bulk/spatial comparison.
Scalar-log identification alone would not close either missing input.
A03, full J02/J03, continuum survival, physical calibration, QFT and every-
group Clay construction remain open. No canonical chart state changed.

### Source review selecting the next spatial frontier

Luna's bounded review, checked against source by root, found the following
distinction. This is source evidence, not another mathematical closure:

- `BF4WilsonAllNomeReflectedForm.intrinsicForm_chart`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeReflectedForm.lean:163`, changes a
  common temporal chart inside ONE width, not the spatial action.
- `BF4WilsonAllNomeDyadicDenseNaturality.inclusion_paddedSquare_loopState`,
  `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicDenseNaturality.lean:45`,
  transports dense syntax. Its header explicitly excludes completed form
  or changing-width response comparison.
- `BF4WilsonSpatialUnionNaturalTransformation.denseToUnion`,
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionNaturalTransformation.lean:91`,
  is a genuine common completed target, but requires the small-nome guards
  declared at lines 55--57 of that file.
- `BF4WilsonSpatialUnionFixedBase.completedInner_map`,
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionFixedBase.lean:110`, preserves
  the LEGACY guarded fixed-base pairing. Its source carrier is not the
  literal all-nome completion used by F.
- `BF4WilsonSpatialUnionTimeForm.completedTime_correlator`,
  `lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeForm.lean:137`, retains
  the original correlator and time, with those same guards.

The guards include `heatRatio w <= 1/2`, `heatRemainderBound w < 1` and
`entropyRate 625 (adjustedCoreRate w hd) < 1`. `heatRatio` and
`heatRemainderBound_eq` in
`lean/YMGap/Continuum/QuaternionHaarCharacterInterval.lean:80` and `:85`
give 32*w^3 and 128*w^3 respectively. These guards therefore exclude a
nome approaching 1; they cannot be silently dropped from the spatial
consumer. No completed comparison applicable in that regime was found in
the modules just listed. The next missing producer is actual interior-
observable form/correlation control as width and coupling change, not
another dense syntactic naturality identity or a generic operator wrapper.

## Verification and coordination

Sol proved completed pairing continuity and the represented-row estimates;
Luna proved finite symmetry/positivity. Root passed those facts to the
already constructed F and derived linearity by pairing extensionality.
Sol independently reviewed the final mathematical chain and scope.

All checks were sequential via `scripts/safe_lean_build.py --jobs 1
--status-seconds 300 --check-worker-limit-gib 20 --check ... --check-output ...`.
Dynamic memory monitoring stayed active. No long-running check needed polling.

| File | Final result | Printed gates |
| --- | --- | --- |
| `BF4WilsonAllNomeCompletedPairingContinuity.lean` | passed | 10 |
| `BF4WilsonAllNomeRowPairingLimit.lean` | passed | 16 |
| `BF4WilsonAllNomeLogPartialAlgebra.lean` | passed | 2 |
| `BF4WilsonAllNomeLogOperator.lean` | passed | 11 |

All 39 printed axiom sets lie within {propext, Quot.sound}. No sorryAx,
classical axiom, new analytic assumption, or weakened frontier field.
The finite zero-case elaboration failures were repaired before final checks.
No sorry was introduced or discharged. No full-root/full-tree build,
full audit or guard run was performed.

Logs are `lean/.lake/allnome-completed-pairing-continuity-check.log`,
`lean/.lake/allnome-row-pairing-limit-check.log`,
`lean/.lake/allnome-log-partial-algebra-check.log`, and
`lean/.lake/allnome-log-operator-check.log`.
