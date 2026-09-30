# The original conditional inverse approximants preserve gauge invariance

Date: 2026-09-30 UTC. Eight focused checks passed all 31 public axiom gates;
independent Luna/Sol scope review passed. No strict covariance estimate or
completed invariant-sector theorem is claimed.

## Actual output and consumer

`conditionalRep_invariant` at
`lean/YMGap/Continuum/BF4ExactSlabGaugeConditionalApproximation.lean:128`
proves that EVERY polynomial in the existing conditional Cauchy
representative retains the existing original-polynomial `Invariant`
predicate, given that predicate for its input. The theorem is quantified
over the actual supplied vertex tags, finite physical link list, every
iteration index, rational `0<w<1` and late cutoff.

The predicate is `Invariant` at
`lean/YMGap/Continuum/BF4ExactSlabVertexGaugeAction.lean:60`: supported
original polynomials, compared with their actual common vertex-gauge ledger
images after adjoining three auxiliary Haar blocks. Its tags have type
`Z4Vertex -> Option (Fin 3)`. This checkpoint neither changes that predicate
nor constructs an action of arbitrary independent vertex gauges on the
unaugmented completion.

The exact representative is `conditionalRep` at
`lean/YMGap/Continuum/BF4ExactSlabBlockOriginalConditional.lean:142`.
The existing `conditionalProjection_embed` at
`lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:95`
identifies the completed conditional projection's dense output with this
representative's class. No new conditional operator or Hilbert space is
substituted.

## Causal proof chain

1. A selected translation is a polynomial algebra map preserving Haar.
   Thus a square-null difference remains square-null. Positivity of the
   actual finite Haar form recovers equality against every supported test.
   This is `applySelectedTranslationStep_preserves_supportedHaarEqv` and
   `applySelectedTranslationSteps_preserves_haarCarrierEqv` at
   `lean/YMGap/Continuum/SU2QuaternionSelectedTranslationCarrier.lean:89`
   and `:142`. No inverse/surjectivity assumption replaces this proof.
2. Conditional projections preserve Haar equality by self-adjointness:
   `project_preserves_haarCarrierEqv` and
   `familyProject_preserves_supportedHaarEqv` at
   `lean/YMGap/Continuum/SU2QuaternionHaarCarrierProjection.lean:33`
   and `:68`.
3. Direct selected shears fix already-integrated inputs on the Haar
   carrier: `selectedLeft_project_fixed`, `selectedRight_project_fixed`
   at `lean/YMGap/Continuum/SU2QuaternionSelectedProjectionFixed.lean:76`
   and `:101`. Raw coefficient equality is not asserted: expose/restore
   may pad trailing-zero monomial coordinates.
4. Inverse orientations use conjugation of the multiplier.
   `conjugate_carrier` and `project_conjugate` at
   `lean/YMGap/Continuum/SU2QuaternionConjugationProjection.lean:62`
   and `:107` supply its carrier congruence and distinct-block commutation.
5. `project_step`, `project_steps`, `familyProject_steps` at
   `lean/YMGap/Continuum/SU2QuaternionSelectedProjectionEquivariance.lean:91`,
   `:110`, `:130` compose all four step orientations and finite schedules.
   Each integration index must avoid every step's multiplier. Repeated
   schedule entries are allowed; arbitrary supported input is retained.
6. The actual ledger's multipliers are all below three, proved from
   endpoint-step membership by `gaugeLedger_multiplier_lt_three` at
   `lean/YMGap/Continuum/SU2QuaternionGaugeFamilyProjection.lean:57`.
   Hence every original physical schedule shifted by three qualifies.
   The actual slab specialization is `slabGauge_familyProject` at `:94`.
7. `familyProject_lift` at
   `lean/YMGap/Continuum/SU2QuaternionLiftedFamilyProjection.lean:128`
   identifies the shifted augmented projection with the lift of the
   original projection by LITERAL polynomial equality. No support
   hypothesis is needed for this coordinate identity.
8. The existing original `Invariant` predicate therefore survives family
   integration, multiplication by the actual normalizer, and every step
   of the already constructed inverse recurrence.

The last step's declarations in
`lean/YMGap/Continuum/BF4ExactSlabGaugeConditionalApproximation.lean` are:

| Declaration | Line | Exact scope |
| --- | --- | --- |
| `familyProject_invariant` | 51 | Existing predicate preserved by original physical integrations. |
| `collarHeat_invariant`, `background_invariant` | 69, 74 | Actual incident and detached face products retained. |
| `normalizer_invariant`, `insertedNormalizer_invariant` | 80, 88 | Actual D and N_p, not a floor or alternate law. |
| `approximateInverse_invariant` | 106 | Every constructed iterate preserves invariant input. |
| `conditionalApproximation_invariant` | 117 | Specialization to the actual inserted numerator. |
| `conditionalRep_invariant` | 128 | Every term of the SAME full-action Cauchy representative. |

The originals are `normalizer`, `insertedNormalizer`, `full_marginal_pin`
and `full_inserted_marginal_pin` at
`lean/YMGap/Continuum/BF4ExactSlabBlockNormalizer.lean:64`, `:67`, `:101`
and `:110`. The detached action is not removed or duplicated. The inverse
is `approximateInverse` at
`lean/YMGap/Continuum/BF4ExactSlabBlockInverseApproximation.lean:114`.

## Remaining join, not assumed closed

A closed gauge-invariant sector of the SAME full-action GNS completion,
and preservation of that sector by the completed block projection and
actual auxiliary recurrence, remain unproved here. Termwise invariance
does not by itself construct or characterize that completed sector.
The augmented weighted pairing identity does not automatically supply an
endomorphism of the original completion.

`fixed_of_cauchy_terms` at
`lean/YMGap/Continuum/GNSDenseFixedPoint.lean:79` requires a self-adjoint
completed map already supplied. No such gauge map is assumed here.
`state_mem` at `lean/YMGap/Continuum/GNSChebyshevEnergy.lean:137` consumes
completed-sector zero/add/sub closure and preservation by its operator;
those gauge-sector inputs remain to be constructed on the actual carrier.

More importantly, symmetry provides no useful rho or signed
variance-relative estimate on a justified scaling family. The certificate
consumer `residual_pair_lower_of_certificates` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceCertificate.lean:83`
still has an unsupplied useful certificate family. Collective signed
estimates remain alternatives. No new analytic input bundle is added.
These conditional operators are not the OS transfer. Geometry, scaling,
nontrivial survival, thermodynamic passage, full same-theory QFT axioms,
physical Hamiltonian mass and every compact simple group remain open.
The canonical chart's displayed claims are unchanged.

## Verification boundary

All eight new modules passed focused serialized checks through
`scripts/safe_lean_build.py`, with one worker and a 20 GiB ceiling. All 31
public printed gates stayed within `{propext, Quot.sound}`. The lifting
draft initially acquired `Classical.choice` when automation closed a
conjunction. Explicit conjunction construction followed by scalar arithmetic
proofs removed that dependency; only the clean final checks count.
No new sorry, custom axiom, classical input or weakened frontier remains.

No root/tree build, full audit, guard, broad test suite, progress metric,
Rust computation or new literature scan was run. Root imports are added
without claiming root integration verification. Luna reviewed carrier and
ledger composition; Sol independently checked the final original
normalizer, inverse and Cauchy-representative joins.
