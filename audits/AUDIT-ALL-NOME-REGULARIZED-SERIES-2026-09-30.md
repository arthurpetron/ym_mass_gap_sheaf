# Constructive regularized series on the original Wilson completion

Date: 2026-09-30 UTC. Three final focused checks passed; no broad run.
This checkpoint is historical: its limit norm/linearity/symmetry residue
was subsequently closed in `AUDIT-ALL-NOME-REGULARIZED-OPERATOR-2026-09-30.md`.
Whole-project goal: constructive continuum Yang--Mills on R^4 for every
compact simple group, with the same-theory QFT axioms and a positive finite
physical mass gap. That goal remains OPEN.

## Mathematical increment and actual consumer

For every rational nome 0<w<1 and fixed width, let T be the ORIGINAL
completed one-step Wilson transfer, D=I-T, and B its ORIGINAL completed
inner product. All vectors below lie in
`BF4WilsonAllNomeCompletedInner.Completion hw0 hw1 width`.
No legacy thermodynamic carrier is substituted.

The positive mixed-moment estimate now bounds pairs of filtered vectors:

```
v_i = D^i T x,
B(v_i,v_j) <= B(x,x)/((i+1)(j+1)).

F_N x = sum_{k=1}^N D^k T x/k,
||F_N x - F_M x||^2 <= B(x,x)/(M+1)^2       (M <= N).
```

Indeed, the kth term contributes the reciprocal product 1/(k(k+1)).
The identity 1/(k(k+1)) + 1/(k+1) = 1/k telescopes in each pairing
argument. This proves the finite tail estimate without a spectral theorem,
square root, or a time-injectivity premise.

The actual consumer is `regularizedLog`: the constructive limit of these
finite sums on the SAME completion. For a supplied original Cauchy stream
X, `logTailCauchy` constructs a representative of every partial sum using
the existing time, addition and rational-scalar maps. Let C be its existing
computed nonnegative norm ceiling. The outer Cauchy modulus is

```
seriesModulus X epsilon = max C.num.toNat epsilon.den.
```

At n beyond this cutoff, C/(n+1)<=1 and 1/(n+1)<=epsilon, so
C/(n+1)^2<=epsilon. The represented diagonal limit includes the existing
epsilon/16 loss through `convergenceModulus`. The returned
`regularizedLogCertificate` contains the actual carrier element AND this
modulus and convergence proof as data.

Quotient descent does not choose representatives: equal input classes have
equal finite partial sums, and `limit_independent` identifies their
constructed limits. Their computable moduli need not be equal. The finite
time-commutation and zero laws pass to the limit by the already proved
represented-limit identities and uniqueness.

## Declaration evidence

All paths in this table are relative to `lean/YMGap/Continuum/`.

| Declaration | File:line | Exact content |
| --- | --- | --- |
| `positiveTimeTail_pair_bound` | `BF4WilsonAllNomeLogPartial.lean:89` | Mixed pair bound for actual D^i T x and D^j T x. |
| `logTerm`, `logTail`, `logPartial` | `BF4WilsonAllNomeLogPartial.lean:106`, `:109`, `:114` | Original finite vectors, with k=1..N indexing. |
| `logTail_pair_bound` | `BF4WilsonAllNomeLogPartial.lean:140` | Product reciprocal budget for two finite tails. |
| `logTail_norm_bound` | `BF4WilsonAllNomeLogPartial.lean:180` | Squared-norm tail bound. |
| `logPartial_ordered_distance_bound` | `BF4WilsonAllNomeLogPartial.lean:218` | Actual completed-distance estimate. |
| `logPartial_commutes_time` | `BF4WilsonAllNomeLogPartialLaws.lean:68` | All finite sums commute with every original integer time. |
| `logPartial_kernel_zero`, `logPartial_unit_zero` | `BF4WilsonAllNomeLogPartialLaws.lean:117`, `:160` | Finite sums annihilate the actual T-kernel and vacuum. |
| `logTailCauchy`, `logTailCauchy_pin` | `BF4WilsonAllNomeLogSeries.lean:89`, `:94` | Explicit representatives and exact quotient pins. |
| `seriesModulus`, `logRows` | `BF4WilsonAllNomeLogSeries.lean:105`, `:146` | Inner and outer moduli retained as data. |
| `regularizedLog` | `BF4WilsonAllNomeLogSeries.lean:167` | Actual presentation-independent limit map. |
| `regularizedLog_approximation`, `regularizedLogCertificate` | `BF4WilsonAllNomeLogSeries.lean:180`, `:189` | Quantitative approximation and witness-bearing result. |
| `regularizedLog_commutes_time` | `BF4WilsonAllNomeLogSeries.lean:199` | Limit commutes with original discrete time. |
| `regularizedLog_kernel_zero`, `regularizedLog_unit_zero` | `BF4WilsonAllNomeLogSeries.lean:228`, `:235` | Limit annihilates the actual T-kernel and vacuum. |

## Honest boundary and next work

- The reciprocal coefficient is independent of the explicitly quantified
  nome and width. The absolute convergence modulus depends on the supplied
  vector's computed norm ceiling. N is a polynomial cutoff, not physical
  time, lattice spacing or an inverse mass.
- This is positive-contraction algebra, not a non-abelian coercivity
  mechanism. It proves no beta-uniform physical mass gap.
- The regularization retains T in EVERY summand. Nothing proves convergence
  of sum D^k x/k on all states. The positive-norm finite-width boundary
  kernel is still present and is annihilated by this map, not discarded.
- No theorem here identifies the constructed map with a scalar logarithm,
  the legacy `RegularizedLogPolynomial` action, or an unbounded Hamiltonian.
  A norm bound, linearity and symmetry for the LIMIT map are not asserted
  by these declarations. The norm bound above is for finite tails.
- The construction supplies a concrete same-carrier series with a modulus
  for further functional-calculus work; it does not supply a continuous
  physical-time semigroup, a generator identity, spatial transport or
  changing-spacing control. Any generator-domain construction must respect
  the actual boundary kernel and justified spatial/scaling passage.
- The primary missing analytic input remains useful original-action signed
  collective control relative to the SAME interacting energy on justified
  scaling. Error control for a finite signed approximation is not a bound
  for its value. A03, full J02/J03 and all continuum/Clay requirements remain
  open. No canonical frontier statement or chart state is changed.

## Independent review while verification ran

The original signed-value question has a guarded producer, not an
unconditional scaling answer. `signedNeighborEnergy_lower` in
`lean/YMGap/Continuum/BF4ExactSlabConditionalGeneratorLowerBound.lean:71`
gives the original signed sum S >= -50*pairCoefficient*E under its
`hsmall` and `hd` guards. `signedNeighbor_error_bounds` in
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:137`
gives |S-V|<=d*E at the computed approximation cutoff, on the SAME energy.
Together these imply V>=-(50*pairCoefficient+d)*E. This combination was
reviewed as a mathematical consequence, not added as a new Lean theorem:
it retains the existing small-nome guards and gives no new scaling producer.
`residual_pair_decomposition` in
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:168`
retains the positive defect square minus prediction covariance; it does
not bound that covariance. The normalized-feature matrix criterion in
`AUDIT-NORMALIZED-FEATURE-CERTIFICATE-DOMAIN-2026-09-30.md` remains paper-only.

The next short same-carrier functional-calculus input is quantitative
pairing continuity along represented rows: it would pass the finite norm
cap to the limit. Existing legacy thermodynamic row-pairing theorems act
on a different carrier and were NOT used as a substitute. Finite linearity
and symmetry and their limit laws also remain to be proved for this map.
These are identified next propositions, not claimed results here.

## Verification and coordination

Sol proved the finite pairing/tail estimates; Luna proved the finite time,
kernel and vacuum laws. Root constructed the represented series limit and
its limit laws. Sol independently reviewed indexing, quotient descent and
scope. Proof work was parallel; all compiler checks were serialized.

Each focused check uses the safe launcher with one worker, a 20 GiB worker
ceiling, automatic dynamic memory protection and 300-second status output:

```
python3 scripts/safe_lean_build.py --jobs 1 --status-seconds 300 \
  --check-worker-limit-gib 20 --check lean/YMGap/Continuum/FILE.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/FILE.olean \
  --log-file lean/.lake/LOG.log
```

| File | Final result | Printed gates |
| --- | --- | --- |
| `BF4WilsonAllNomeLogPartial.lean` | passed | 10 |
| `BF4WilsonAllNomeLogPartialLaws.lean` | passed | 3 |
| `BF4WilsonAllNomeLogSeries.lean` | passed | 21 |

All 34 printed axiom sets are within {propext, Quot.sound}; none contains
sorryAx or a classical axiom. Initial elaboration failures were repaired
before these final checks. The final series check was left running while
independent source review and mathematical documentation proceeded, rather
than repeatedly polling its status.

Logs: `lean/.lake/allnome-log-partial-check.log`,
`lean/.lake/allnome-log-partial-laws-check.log`,
`lean/.lake/allnome-log-series-check.log`.
No full-root/full-tree build, full axiom audit or guard run was performed.
No sorry was introduced or discharged, and no new axiom, named analytic
premise, surrogate substitution or canonical frontier weakening was added.
