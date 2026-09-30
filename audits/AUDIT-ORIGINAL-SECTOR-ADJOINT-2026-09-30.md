# Dense original derivative domain and intrinsic sector adjoint

Date: 2026-09-30 UTC. Classification: PROGRESS. The real derivative graph
is densely defined, closed, and equal to its intrinsic adjoint on the
presented original time-range sector. No physical OS identification or
continuum/Clay closure is asserted.

## Mathematical construction

Let T be the ORIGINAL one-step transfer and A the previously constructed
derivative on preimages, so the original graph core is (Tx,Ax). Keep a
sector state as its original completed vector together with its explicit
`RangeLimit` witness. Equality compares the vector, not its witness.

This choice solves the actual representation issue: every sector sequence
already supplies the data from which original Cauchy representatives can
be computed. The existing represented completion therefore constructs its
limit with no countable selection. Its convergence rate retains the
existing diagonal's e/16 loss, rather than silently reusing the Cauchy
modulus at e. Range closedness supplies the limit's sector witness.

A domain point consists of two such sector states u,v satisfying the
proved graph criterion Au=Tv. The graph and inverse-sum source streams
are constructed from those data; the definition does not assume a new
operator or a new analytic theorem. The original graph's uniqueness makes
the output independent of the input presentation. Its inclusion into the
old graph domain preserves both input and action exactly, without claiming
that every old-domain source sequence has selected representatives.

The additional density argument now has its actual codomain: for a sector
state x with witness R, use core points

    ( T(Class(R.preimage n)), A(Class(R.preimage n)) ).

The first coordinate has the literal time-image range witness. The second
has the previously constructed output-range witness for the represented
core graph. Thus BOTH coordinates lie in the sector, and `R.bound` is the
computed domain-density estimate with cutoff `R.modulus`.

Define the intrinsic adjoint condition for sector states u,v by

    B(u,p.output) = B(v,p.input)   for EVERY actual domain point p.

It is not a vacuous test family: it includes every represented core point.
Testing those points gives the original core pairing condition. Quotient
induction into this Prop-valued condition, followed by the existing bounded
A/T symmetry argument, proves Au=Tv. Hence an adjoint pair CONSTRUCTS a
point of this same domain. Graph symmetry proves the converse. No
resolvent, representative selection, or physical-sector premise is used.

For simultaneous Cauchy input/output sequences satisfying the equation,
the original graph diagonal proves that their computed sector limits
satisfy it too. The domain is closed in this explicit graph-norm sense.
Addition and supplied-modulus real scaling preserve it. Finally, the
stored range witnesses compute both coordinate representatives, so the
existing all-small-positive-real-time Taylor certificate applies to every
domain point. The original fixed-nome/width form margin (1-q)/2 is retained.

## Checked source map

All abbreviated module names below have prefix `BF4WilsonAllNome` and are
under `lean/YMGap/Continuum/`.

| Declaration | Source | Exact role |
|---|---|---|
| `State`, `stateSetoid` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:43`, `:48` | Witness-bearing states with equality of underlying vectors. |
| `fromTime`, `zero`, `add`, `negate`, `realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:53`, `:59`, `:63`, `:67`, `:71` | Actual original-sector linear operations and core inputs. |
| `CauchySequence`, `representedRows`, `representedRows_point` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:78`, `:86`, `:97` | Sequence representatives computed from stored witnesses, with exact pins. |
| `limit`, `limitRate`, `limit_bound`, `limit_unique`, `limitCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeTimeSector.lean:102`, `:110`, `:114`, `:123`, `:136` | Explicit sector completeness and uniqueness of underlying limit. |
| `DomainPoint`, `graph`, `sourceRepresentative`, `sourceRepresentative_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:68`, `:74`, `:80`, `:84` | Same-sector graph with actual original source data. |
| `toOriginalDomain`, `original_input_pin`, `original_action_pin`, `originalDomain_eq_iff` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:91`, `:96`, `:100`, `:115` | Exact inclusion in the unchanged old domain. |
| `domainSetoid`, `output_congr`, `add`, `realSmul` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:104`, `:109`, `:122`, `:130` | Extensional operator output and actual real-linear domain operations. |
| `corePoint`, `coreApproximation`, `coreApproximation_bound`, `coreDensityCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:137`, `:144`, `:147`, `:153` | Both core coordinates inhabit the sector; computed domain density. |
| `AdjointPair`, `domain_adjoint`, `adjoint_equation`, `ofAdjoint`, `equation_iff_adjoint` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:161`, `:164`, `:170`, `:179`, `:184` | Intrinsic real graph-adjoint equality and constructive converse. |
| `closedLimit` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:190` | Simultaneous sector limits stay in the original derivative graph. |
| `realTaylorCertificate`, `domain_nonnegative`, `domain_form_gap` | `lean/YMGap/Continuum/BF4WilsonAllNomeSectorDerivative.lean:217`, `:233`, `:236` | Original-time derivative, positivity, and fixed-parameter margin. |

## Scope and next causal boundary

This is intrinsic REAL graph self-adjointness on the presented/setoid sector.
Literal equality of `State` structures is not vector equality: witnesses
remain stored. No quotient of these witnesses is assumed to retain a
computable section, and completeness for arbitrary sequences in a
witness-erasing quotient is not claimed. The old `DerivativeGraph.Domain`
is unchanged; only the proved inclusion is supplied.

The full complex Hilbert/OS reconstruction and physical-sector identification
remain OPEN, as do physical-time/mass calibration, spatial/scaling control,
nontrivial continuum survival, Yang--Mills local-field/UV content, and every
compact simple group. The fixed-parameter form bound is not a physical
spectral-gap theorem. The ambient boundary kernel remains present. Equality
with the separate regularized-log series is neither assumed nor needed here.

Do not continue this branch by re-proving another equivalent pairing
criterion. The next reconstruction join needs an actual SAME-object
physical OS/observable comparison (and its complex structure), not the
legacy total-map Hamiltonian placeholder. The independent primary analytic
frontier remains the SAME-source signed temporal-energy/variance UPPER
estimate on a justified scaling family; nothing here supplies that estimate.

## Verification and review

Two final focused serialized checks passed 37 printed gates: 13 for
`TimeSector`, 24 for `SectorDerivative`, all exactly {propext, Quot.sound}.
The TimeSector draft's extra T in a representative pin and omitted e/16
modulus loss were corrected by main before its first check. The derivative
module's first check exposed missing explicit width arguments and the need
to supply both coordinate representatives to the Taylor consumer; these
were fixed without changing the proposition. Both final logs are clean.

Luna drafted TimeSector. Main corrected its witness/rate flow, wrote the
domain/density/adjoint construction, and ran all checks. Sol independently
reviewed the representation discipline, density, adjoint equivalence,
closed-limit construction and computed Taylor representatives.

The safe-build skill kept verification targeted: one worker, mandatory
20 GiB cap, 12 GiB OS reserve, process/memory preflight and automatic safety
telemetry. No safety stop, raised limits, full-tree/root build, audit, guard,
progress script, new sorry/axiom, or canonical frontier weakening. Added
root imports are not a root build. The canonical chart is unchanged.

Final logs and SHA-256:

- `/tmp/ym-wilson-time-sector-20260930.log`:
  `1219dfcf24a6e95e062e22861640d6c8251dd990e8f4421a798ce3c5d8440104`
- `/tmp/ym-wilson-sector-derivative-20260930.log`:
  `219525e22881c69ecce843e04b8bde0f56fd0473c8386dd211d5827eb13981b1`
