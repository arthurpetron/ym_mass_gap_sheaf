# Original completed prediction covariance and signed residuals

## Result and exact scope

For the actual original block projections `P_A`, `P_B`, and
`C=P_(A++B)`, put `R_A=I-P_A`, `R_B=I-P_B`, and
`d=x-P_A x-P_B x+C x`. The new checked identity is

    <R_A x,R_B x> = ||d||^2 - (<P_A x,P_B x> - ||C x||^2).

The subtracted term equals `<P_A x-C x,P_B x-C x>`. These are the
constructed projections on the SAME original full-action completion, not
free-product/reference projections. The statement covers every completed
state, finite physical block lists including overlap, rational `0<w<1`,
and `K>=headCutoff(w)`. It does not assume `P_A P_B=P_B P_A` or assert that
the common projection is the entire intersection of their ranges.

- Generic identity: `lean/YMGap/Continuum/GNSProjectionPredictionCovariance.lean:76`,
  `residual_pair_prediction_decomposition`.
- Actual instance: `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:168`,
  `residual_pair_decomposition`.
- Common-part removal: `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:156`,
  `predictionCovariance_centered`.

## The actual normalizer reaches the prediction arguments

`predictionRep` constructs the existing cofinal diagonal from a supplied
input Cauchy representative. `predictionRep_class`, `predictionRep_modulus`,
and `predictionRep_independent` identify its completed class, retain the
explicit `gMod`, and prove every term independent of the integrated block.
The diagonal's sampling indices still depend on the input and the original
conditional approximation; `gMod` is not a mixing or scaling rate.
Sources: `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:57`,
`:60`, `:66`, `:72`, respectively.

For any two supplied Cauchy representatives X,Y, `inverseCovarianceSequence`
pairs their dense conditional covariance numerator through the ACTUAL union
normalizer inverse, against the unit of the detached background. If the
full action is E*W and D=P(W), this is E*N/D, not E*N or N divided by a floor.
`inverseCovarianceSequence_converges` proves convergence to the explicitly
constructed CReal `covarianceLimit`, using the supplied Cauchy data and joint
pairing continuity. For the two prediction representatives,
`prediction_covariance_limit` identifies that limit's class with the exact
subtracted term in the residual decomposition.
Sources: `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:87`,
`:113`, `:94`, `:182`, respectively.

Only supported dense polynomials are multiplied inside the numerator.
There is no arbitrary completed multiplication or representative selection.
The pairing is unnormalized by the total full partition, as is `fullData`;
normalizing both sides uses the same positive scalar.

## Consumer and remaining mathematics

`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142`,
`neighboringCross_lower`, consumes actual residual-pair lower bounds.
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborEnergy.lean:68`,
`conditionalGenerator_square`, retains the signed neighbor sum alongside
the positive remote remainder. The new identity identifies what signed
quantity must be estimated for those consumers; it does NOT supply the bound.

NEXT: estimate the original inverse-normalized prediction covariance together
with its positive defect, relative to actual residual energy, on a justified
scaling family. Dropping the defect and bounding covariance alone is a
stronger sufficient approach, not a necessary physical requirement. Retain
the actual one-sided action factors. A collective bound may preserve more
cancellation than independent absolute pair bounds.

For the existing two-link four-copy formula, a `P_A` approximant is independent
of A and a `P_B` approximant of B. Its convention requires f independent of B
and g independent of A: use the predictions in that opposite order. The
generic block result does not itself generalize the two-link determinant
factorization to arbitrary overlapping blocks. Source of the convention:
`lean/YMGap/Continuum/BF4ExactSlabTwoLinkFourCopy.lean:255`,
`original_shared_four_copy_identity`.

The parallel Ward review prevents a separate unjustified shortcut:
`lean/YMGap/Continuum/BF4ExactSlabWardFamilyCost.lean:115`,
`totalScore_cost_le`, and `:136`, `totalScore_response_bound`, require
star-local per-link tests to obtain their factor 25. Arbitrary supported f
is only the paired observable. Global f-dependent tests cannot inherit that
factor without a locality or replacement cost proof. Existing designed
plaquette-gradient responses do not establish an arbitrary-projection bound.

No useful covariance coefficient, range-angle estimate, block schedule
geometry, physically justified scaling, nontrivial continuum survival,
thermodynamic limit, OS/Hamiltonian bridge, full same-theory QFT or every-group
Clay result is closed. The generic identity uses only Hilbert/projection
algebra; it is not a new nonabelian analytic estimate.

## Verification

Both new targets passed focused serialized checks using
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`.
All 16 printed gates are contained in `{propext, Quot.sound}`; none contains
`sorryAx`. Luna independently reviewed the mathematics and scope. No new
sorry, axiom, analytic assumption bundle, weakened frontier, numerical
certificate, broad build/audit/guard/progress run, or CI run. The root imports
were registered but the root target was not rebuilt. Canonical chart block
unchanged; this is a supporting identity/approximation join, not closure of
its displayed analytic bound.
