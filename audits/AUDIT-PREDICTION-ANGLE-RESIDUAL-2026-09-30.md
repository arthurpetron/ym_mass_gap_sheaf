# Prediction covariance to signed residual energy

Date: 2026-09-30 UTC. Focused verification passed.

## Mathematical result

For the SAME original completed block projections, write
`C=P_(A++B)`, `y=x-Cx`, `u=P_A x-Cx`, `v=P_B x-Cx`.
The existing reverse towers give `<y,u>=||u||^2` and
`<y,v>=||v||^2`. Put `c=<u,v>`, `V=||u||^2+||v||^2`,
`E=||y-u||^2+||y-v||^2`, `r=<y-u,y-v>` and
`z=(1+rho)y-u-v`. The exact identity is

```
2(1+rho)r + rho(1+rho)E
  = 2||z||^2 + (1-rho)(rho V - 2c).
```

Consequently `0<=rho<=1` and `2c<=rho V` at this state imply
`r>=-(rho/2)E`. The square is retained before using nonnegativity;
there is no `1/(1-rho)` loss and no absolute-covariance premise.

Declarations:

- `lean/YMGap/Continuum/RCPredictionAngleBudget.lean:91`,
  `residual_lower`: constructive scalar order argument.
- `lean/YMGap/Continuum/GNSPredictionAngleResidual.lean:94`,
  `weighted_square_identity`: exact completed-Hilbert identity.
- `lean/YMGap/Continuum/GNSPredictionAngleResidual.lean:182`,
  `projection_residual_lower`: common-subprojection specialization;
  only reverse towers and the displayed one-state covariance bound.
- `lean/YMGap/Continuum/BF4ExactSlabBlockPredictionAngle.lean:53`,
  `residual_pair_lower_of_prediction_bound`: original physical blocks,
  including overlapping blocks, strict rational nome and late cutoff.

## Same-object dense input

`BF4ExactSlabBlockPredictionAngle.covarianceLimit_diagonal` at
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionAngle.lean:79` identifies
the diagonal conditional covariance limit with the actual residual norm.
`prediction_variance_sum_limit` at line 98 gives precisely V above.
`residual_pair_lower_of_dense_covariance_bound` at line 116 passes
`2*N_AB(n)<=rho*(N_AA(n)+N_BB(n))` along the supplied prediction
approximants to the completed residual-pair estimate with the same rho.

Here N is the already constructed inverse-normalized covariance pairing,
not a numerator with the denominator dropped. Its definition and convergence
are `inverseCovarianceSequence` and `inverseCovarianceSequence_converges`,
`lean/YMGap/Continuum/BF4ExactSlabBlockPredictionCovariance.lean:87` and
`:113`. `covariance_normalizer_pair` at
`lean/YMGap/Continuum/BF4ExactSlabBlockCovarianceNormalizer.lean:139`
keeps the actual conditional normalizer D and detached action E once.
This does not introduce a normalization by the global partition function.
The explicit Cauchy representatives and their existing moduli are supplied;
no representative is selected by choice.

## Consumer and limits

`GNSProjectionSweep.Family.neighboringCross_lower` at
`lean/YMGap/Continuum/GNSProjectionNeighborLowerBound.lean:142` consumes
exactly this pairwise residual lower-bound shape with `e=rho/2`.
Its separate row/column degree hypotheses remain required; the coefficient
in its conclusion is `2*degree*e`. This report does not construct a block
schedule or prove the needed covariance input for its neighbor pairs.

The input may be established at states of a specified auxiliary recurrence;
the conversion itself does not demand a bound on every centered state.
It is a sufficient pairwise route, not a necessary condition for mass
generation. Collective signed estimates remain available alternatives.
In particular, no fixed dimensionless gap is imposed as a physical scaling
requirement, and the known isolated-shared-heat obstruction is not bypassed.

OPEN: a useful original-action covariance/variance estimate on justified
scaling, block geometry, nontrivial survival, thermodynamic control and
same-theory OS/QFT/physical Hamiltonian mass for every compact simple group.
These are ordinary full-action conditional projections, not OS time transfer.
No canonical frontier field or chart claim is closed by this conditional
conversion. No new analytic input bundle is introduced.

## Verification

The three new modules passed serialized focused checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check ...`,
with checked `.olean` output for the downstream imports. All 10 printed
declaration gates report only `{propext, Quot.sound}`. No new sorry, axiom,
classical input or weakened frontier. No full-root build/audit/guard was run;
adding root imports does not claim such an integration check. Luna's
independent read-only review found no missing mathematical premise or
normalization mismatch.

During validation, the generic projection-family variable needed its carrier
spelled explicitly as `S.toGNSData`; the shorthand annotation elaborated to
a spurious sorry-bearing type. The final printed gates above confirm its
removal. Compile exit status alone was not accepted as the axiom gate.
