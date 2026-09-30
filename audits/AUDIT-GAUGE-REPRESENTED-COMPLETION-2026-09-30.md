# Original gauge-polynomial representatives through completion and recurrence

Date: 2026-09-30 UTC. Six focused targets passed all 41 public axiom gates
within {propext, Quot.sound}. No strict estimate or continuum result is claimed.

## Mathematical output

The existing block and single-link star projections are the SAME operator
on every vector of the original full-action completion. Each fixes the
other's dense output representatives; continuity extends both inclusions.
Self-adjointness then identifies their pairings, hence the operators.
This is `conditionalProjection_singleton` at
`lean/YMGap/Continuum/BF4ExactSlabBlockSingletonProjection.lean:159`.
It does not compare inverse iterations coefficientwise or replace the
original action by a comparison weight.

An explicit represented invariant-polynomial sector is preserved by the
actual block projections and the existing star sweep, balanced product,
affine map and BOTH components of the coupled recurrence. The constructions
return Cauchy representatives with moduli, termwise invariant predicates,
and equality to the specified point of the SAME completion. No quotient
representative is chosen from a proposition.

## Declaration map

| Result | Declaration and source |
| --- | --- |
| Data-bearing representative and pin | `GNSRepresentedSector.Representative`, `lean/YMGap/Continuum/GNSRepresentedSector.lean:26` |
| Literal diagonal preserves the dense predicate | `Representative.lim_terms`, `lean/YMGap/Continuum/GNSRepresentedSector.lean:68` |
| Supplied diagonal limit witness | `Representative.limit`, `lean/YMGap/Continuum/GNSRepresentedSector.lean:74` |
| Existing dense-map extension preserves witnesses | `Representative.map`, `lean/YMGap/Continuum/GNSRepresentedSector.lean:79` |
| Existing invariant predicate for every tag map | `GaugePolynomial`, `lean/YMGap/Continuum/BF4ExactSlabGaugeRepresentedCompletion.lean:45` |
| Actual completed block projection | `block`, `lean/YMGap/Continuum/BF4ExactSlabGaugeRepresentedCompletion.lean:103` |
| Singleton block is the actual star operator | `conditionalProjection_singleton`, `lean/YMGap/Continuum/BF4ExactSlabBlockSingletonProjection.lean:159` |
| Actual sweep, arbitrary order/repetitions | `sweep`, `lean/YMGap/Continuum/BF4ExactSlabGaugeSweep.lean:54` |
| Actual balanced operator and rational affine map | `balanced`, `affine`, `lean/YMGap/Continuum/BF4ExactSlabGaugeSweep.lean:60`, `:65` |
| Both actual coupled recurrence components | `coupled`, `lean/YMGap/Continuum/BF4ExactSlabGaugeSweep.lean:71`; `state_representatives`, `lean/YMGap/Continuum/GNSRepresentedSectorRecurrence.lean:25` |
| Original finite-mean centering preserves invariance | `centered_polynomial`, `lean/YMGap/Continuum/BF4ExactSlabGaugeCenteredWitness.lean:43` |
| Same-class representative simultaneously invariant and centered | `centered_rep`, `lean/YMGap/Continuum/BF4ExactSlabGaugeCenteredWitness.lean:54` |
| Centering retains the supplied Cauchy modulus | `centered_rep_modulus`, `lean/YMGap/Continuum/BF4ExactSlabGaugeCenteredWitness.lean:66` |
| Both auxiliaries have simultaneously centered/invariant terms | `coupled_centered_reps`, `lean/YMGap/Continuum/BF4ExactSlabGaugeCenteredWitness.lean:72` |
| Actual centered lower/upper plaquette inputs | `lower_input`, `upper_input`, `lean/YMGap/Continuum/BF4ExactSlabGaugeCenteredWitness.lean:84`, `:91` |

## Exact scope

- The dense predicate is the existing `Invariant` at
  `lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:60`, quantified
  over all supplied maps `Z4Vertex -> Option (Fin 3)`. It compares the
  original polynomial with its common-auxiliary vertex ledger image on
  the augmented Haar carrier. No action of arbitrary independent vertex
  gauge elements on the unaugmented completion is constructed here.
- This is a represented sector, not a characterization of every fixed
  vector of an intrinsic completed gauge action. Sequential limits use
  supplied `GeneralCompletionCauchy` representative families and moduli;
  no representatives are extracted from arbitrary quotient-valued families.
- `centered_rep` assumes the specified completed input is already
  orthogonal to the original constant. The existing
  `centeredCauchy_same_class` at
  `lean/YMGap/Continuum/BF4ExactSlabConditionalCenteredCompletion.lean:192`
  supplies the pin; raw Wilson inputs are first actually centered.
- Lower/upper inputs range over `PlaquetteExpression`, not every Wilson
  loop. They do not establish a positive completed norm or a nonzero
  continuum excitation. The reflected upper polynomial remains in the
  ordinary full-action space, not a newly identified OS quotient.
- The sweep is ordinary conditional dynamics. No OS-transfer or physical
  Hamiltonian identity is asserted. No coupling/volume/spacing-uniform
  strict constant is produced by gauge symmetry.

## Actual consumer and remaining analytic input

`finiteCovariance_sq_bound` at
`lean/YMGap/Continuum/BF4ExactSlabChebyshevCovarianceBound.lean:102`
needs reverse energy only at its actual second coupled component,
starting from the embedded ORIGINAL centered polynomial. It does not
require an all-state strict theorem. The new constructions provide
simultaneously invariant and centered approximants to exactly that state
for invariant inputs, including the original plaquette expressions.

The missing quantitative input is still that useful original-action
reverse-energy/signed estimate on justified scaling. The existing optional
pairwise certificate route is `residual_pair_lower_of_certificates` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:83`:
it needs actual signed covariance certificates, not sector witnesses.
Collective signed bounds remain alternatives. No new analytic input bundle
is added and no existing frontier field is weakened. In particular no
fundamental-feature cancellation follows from any declaration added here;
sector preservation must not be used as a quantitative cancellation theorem.
The already-proved small-nome bounds are not a substitute for the missing
justified scaling-family estimate.

The canonical chart is unchanged. A03, physical scaling and nontrivial
survival, thermodynamic control, same-theory OS/QFT/physical mass and every
compact simple group remain open. Earlier completed-sector-open entries
are historical only in the explicit represented-sector scope proved here.

## Verification boundary

All six new modules passed focused checks, serialized through the
safe launcher with one worker, 20 GiB worker cap and continuous memory
telemetry. Luna independently reviewed the representative/diagonal scope
and singleton-to-sweep and centered-input joins; Sol supplied the projection identity and
reviewed the original centering/plaquette source path. No full root build,
full-tree build, audit, guard or progress-metric run is claimed.

| Checked module | Public gates |
| --- | ---: |
| `GNSRepresentedSector` | 10 |
| `GNSRepresentedSectorRecurrence` | 1 |
| `BF4ExactSlabGaugeRepresentedCompletion` | 13 |
| `BF4ExactSlabBlockSingletonProjection` | 5 |
| `BF4ExactSlabGaugeSweep` | 5 |
| `BF4ExactSlabGaugeCenteredWitness` | 7 |

Every final check exited successfully and reported only permitted axioms.
No new sorry, axiom, classical or noncomputable declaration was introduced.
Root imports and documentation were updated; root integration was not run.
