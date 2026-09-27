# Actual original completed block projection

Date: 2026-09-27 UTC. Starting commit: `71ede6a`.
Whole-project target remains open: nontrivial continuum Yang--Mills on R^4
for every compact simple group, with same-theory QFT structure and positive
physical Hamiltonian mass gap, constructively within the repository axiom gate.

## Result and exact scope

`conditionalProjection` at
`lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:90`
constructs the actual finite-block conditional map on EVERY vector of
`GNSCompletionSpace (fullData hw0 hw1 K extent hK)`, using the original
full-action datum `fullData` at
`lean/YMGap/Continuum/BF4ExactSlabStarFullActionProbe.lean:49`.
The hypotheses are rational `0<w<1`, `K>=headCutoff(w)`, and a finite list of
physical links. Empty/repeated lists are allowed. No small-nome guard is used.

In the projection module, the following are proved:

| Declaration | Line | Claim on the same original completion |
| --- | --- | --- |
| `conditionalProjection_nonexpansive` | 98 | All-vector squared distances do not increase. |
| `conditionalProjection_selfAdjoint` | 104 | Actual completed pairing is symmetric under the operator. |
| `conditionalProjection_fix_exterior` | 124 | Fixes an explicitly termwise exterior-independent Cauchy state. |
| `conditionalProjection_fix_exterior_polynomial` | 137 | Fixes every supported exterior-independent polynomial. |
| `conditionalProjection_idempotent` | 150 | Q(Qx)=Qx for every completed x. |
| `conditionalProjection_norm` | 158 | Norm ceiling is one, not a strict rate. |
| `conditionalProjection_positive` | 165 | Positive Hilbert form, not an asserted Markov-order property. |
| `conditionalProjection_residual_orthogonal` | 173 | Input residual is orthogonal to the operator range. |

This is an ordinary interacting weighted-L2 construction. It is not an OS
transfer matrix, a block-pair angle estimate, or a continuum mass-gap theorem.

## Constructive argument and data

Write B for the exact detached original action, D for its integrated incident
collar, and N_p for the actual inserted numerator. The preceding milestone's
proved coefficients L and U give `L I<=D<=U I` in the B form. Neither the
normalizer nor its positivity/coercivity is an assumed analytic certificate.

1. `blockRatio` and `inverseRate` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockInverseApproximation.lean:37` and
   `:52` define `L/U` and `q=1-L/U`. `inverseRate_bounds` (`:55`) proves
   `0<=q<1`. `approximateInverse` (`:114`) starts at zero and iterates
   `a_(n+1)=a_n+(r-D*a_n)/U`. `approximateInverse_residual_norm` (`:137`)
   proves `||r-D*a_n||_B^2<=q^(2n)||r||_B^2`. `approximationCutoff` (`:166`)
   returns a Nat tolerance threshold, including zero input norm and zero rate.
2. `insertedNormalizer_weighted_norm` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockInsertedNorm.lean:70` proves
   `||N_p||_B^2<=U||p||_full^2`. The short argument uses the exact test pairing
   (`insertedNormalizer_pair_pin`, `:47`), original full-action Cauchy--Schwarz,
   the actual collar comparison, and constructive positive/null cancellation.
   It does not discard spectator dependence or replace the input norm by Haar.
3. `approximateInverse_independent` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockConditionalApproximation.lean:46`
   proves that division never reintroduces an integrated coordinate.
   `conditionalApproximation_relative_error` (`:96`) bounds the squared
   division residual by `epsilon*||p||_full^2`, with explicit `relativeCutoff`
   (`:92`) depending only on nome, block size and epsilon.
4. `inverseCauchy` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockCompletedInverse.lean:84`
   uses the residual cutoff at `L^2*epsilon/4`. `inverseState` (`:105`) is the
   resulting completed preimage of a DENSE polynomial source.
   `normalizerCompletion` (`:160`) extends actual multiplication by D;
   `normalizerCompletion_injective` (`:175`) proves injectivity.
   `inverseImageNull` (`:194`) retains an explicit null modulus, and
   `normalizer_inverseState` (`:205`) proves the exact image identity.
   An inverse function on all completed source vectors is not asserted here.
5. `toFullCauchy` and `toFullNullModulus` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockOriginalConditional.lean:90` and
   `:102` keep the literal polynomial sequence and rescale its modulus by
   the proved U comparison. `conditionalRep` (`:142`) and `conditionalUpdate`
   (`:147`) therefore live in the ORIGINAL full-action completion.
6. `toFull_pair_of_independent` and `toFull_test_of_independent` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockOriginalConditional.lean:154` and
   `:175` require independence of EVERY term of the relevant Cauchy
   representatives. `inverseCauchy_independent` (`:191`) supplies it for the
   actual outputs. The finite input is `original_exterior_pair` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockExteriorPairing.lean:54`.
   No arbitrary background-completion vector is called exterior.
7. `conditionalUpdate_pairing` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockOriginalConditional.lean:228`
   proves `<Qp,Qq>_full=<Qp,q>_full`. The square of a difference gives sharp
   dense nonexpansiveness; `conditionalDenseMap` at
   `lean/YMGap/Continuum/BF4ExactSlabBlockConditionalProjection.lean:85`
   supplies the existing constructive completion extension. Dense testing
   then proves self-adjointness, exterior fixation and idempotence.

The inverse algorithm's q is NOT a correlation/mixing rate. Its L/U depends
on nome and selected-link count. The sharp projection norm ceiling is one;
neither the algorithm nor this non-strict ceiling supplies a physical gap.

## Next mathematical consumer: not another inverse wrapper

The source route's all-vector generator-square consumer is
`energy_contract` at
`lean/YMGap/Continuum/GNSResidualGeneratorDescent.lean:112`.
Ordered signed pair estimates are summed by `neighboringCross_lower` at
`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`.
The current SINGLE-LINK instantiation is `signedNeighborEnergy_lower` at
`lean/YMGap/Continuum/BF4ExactSlabConditionalGeneratorLowerBound.lean:71`
and `conditionalGenerator_square_lower` (`:94`); it retains the small-nome
guard and uses the proved degree-25 geometry.

The new operators permit the actual block residual `R_b=I-Q_b` to be used in
the proposed estimate

```
<R_b x,R_c x> >= -e*(||R_b x||^2+||R_c x||^2).
```

This estimate is NOT proved by this milestone. Nor is a block schedule's
cover, neighbor row/column count, remote-residual decomposition or propagation
cone supplied automatically. These must be established on the constructed
operators before importing a sweep/coercivity/covariance argument. In
particular the single-link degree 25, loss 625 and sixteen-layer separation
are not declared to be block constants.

The intended physical requirement is useful decay after actual length/time
calibration on a justified scaling family, together with finite-time survival
and same-observable transport. A uniformly positive dimensionless block margin
would be stronger than some possible calibrated routes require; it is not
imposed as a new necessary hypothesis. Conversely, pointwise positive lattice
margin does not establish the physical conclusion. This is a planning boundary,
not a new physical-rate theorem.

The supplied-AF-chart obstruction from the preceding audit still excludes
simply reusing the old small-nome guard. Selected-face signed boundary response,
thermodynamic/scaling control, same-theory OS/QFT, nontrivial survival,
Hamiltonian mass calibration and every compact simple group remain open.

## Verification and review

Final focused target gate counts: inverse approximation 12; inserted norm 2;
conditional approximation 7; completed preimages 14; exterior pairing 2;
original conditional state 13; completed projection 16. All 66 printed gates
are within `{propext, Quot.sound}`, with no `sorryAx` in successful checks.
Checks used `scripts/safe_lean_build.py`, one worker, 20 GiB ceiling, serialized.
All checks completed in the initial tool call; no heavy job required polling.

Sol proof tasks and Luna source/scope reviews ran in parallel without concurrent
compilers. Review confirmed original-carrier preservation, explicit exterior
independence and the distinction between inverse rate and dynamics rate. The
initial overly strong planning suggestion of a uniform dimensionless margin
was corrected before publication; it was never added as a Lean hypothesis.

No new sorry, axiom, analytic bundle, canonical field/marker change or CI.
Root imports are registered; no root/full-tree build, full audit, guard or
progress-metric run was performed. The canonical chart is unchanged and is
not reprinted. This is a checked block-operator construction, not Clay closure.
