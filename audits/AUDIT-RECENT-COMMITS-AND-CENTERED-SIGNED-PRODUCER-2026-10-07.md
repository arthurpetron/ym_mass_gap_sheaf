# Recent-commit review and the actual centered signed producer (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms
and a positive physical Hamiltonian mass gap.

## Review boundary

Reviewed Git history for 2026-10-05 through 2026-10-07, ending at `8c6e113a`:
280 commits (11, 78, 191 by recorded date). This is a history/source review,
not a fresh build or axiom audit of those 280 commits. Commit titles, the
current opening work plan, dated audits and selected load-bearing declarations
were checked. The new proofs below were checked in this session.

## What the recent commits actually changed

| Commits / route | Source evidence | Mathematical scope and remaining input |
| --- | --- | --- |
| `a5c17995`, padded AF schedule | `lean/YMGap/Continuum/BF4WilsonAllNomeAFPaddedTrajectory.lean:286`, `afNomeSchedule_AFCalibrated`; `:303`, `afPaddedZeroMomentumTrajectory`; `:329`, explicit `PathShiftedWindowSurvival` input | Constructs the rational two-loop-shaped schedule and padded state, not its physical spacing calibration or quantitative window survival. |
| `0ec28cd2`, width-uniform strong-coupling route | `lean/YMGap/Continuum/BF4WilsonAllNomeStrongCouplingUniformRate.lean:436`, `allNome_strongCoupling_vacuumSq`; `:443`, `_all_widths` | Same original carrier, width-independent rate, under explicit small-nome guards. Not a contraction along the AF schedule. |
| `1557f350`, finite torus RP | `lean/YMGap/Continuum/SU2TorusRPPolyCS.lean:56`, `torus_rp_poly`; `:60`, `torus_cs_poly` | Actual SU(2) truncated Taylor-Wilson torus measure and positive-half polynomial support. No transfer, continuum limit or every-group claim. |
| `8a347c79`, actual torus moment join | `lean/YMGap/Continuum/SU2TorusCenteredFiniteRatio.lean:33`, `actual_torus_ratio` | Proves the finite scalar consumer with actual support, shift and covariance pins; not an every-state completed estimate. |
| `5e88590d`, `4a0581cf`, repaired RG rate direction | `lean/YMGap/Continuum/BF4WilsonAllNomeRGTwoStepRecovery.lean:58`, `vacuumSq_of_twoStepFactor`; `lean/YMGap/Continuum/BF4WilsonAllNomeRGComputedMargin.lean:372`, `computedWilsonFamily_lowerMargin` | Computes a correct one-step rate and telescopes its own margin, conditional on actual comparisons and budget. Does not inhabit the preserved opposite-direction legacy rate chain. |
| `067111e2`, relative dissipation | `lean/YMGap/Continuum/BF4WilsonAllNomeRGRelativeDissipation.lean:40`, `relativeFactor`; `lean/YMGap/Continuum/BF4WilsonAllNomeRGDissipationBudget.lean:232`, `relativeRate_margin_lower` | Relative error delta times the coarse deficit reduces the sufficient budget to ordinary delta prefix sums. Action-specific comparison and useful delta values remain OPEN. |
| `b883de91`, compatibility of the two fronts | `lean/YMGap/Continuum/BF4WilsonAllNomeRGSlowStateRetention.lean:167`, `shiftedState_retention`; `:182`, `_of_cap` | Survival plus the proposed relative comparison force selective slow-state norm retention. This is necessary compatibility, not construction of either input. |
| `8c6e113a`, exact blocked action | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialGluedEndpointMarginal.lean:169`, `glued_lower_endpoint_pairing`; `:218`, `compressed_lower_endpoint_pairing`; `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCubeGluedHeatOnlyObstruction.lean:73`, `glued_endpoint_not_free` | Keeps K01*V1*K12 and proves its actual marginal. The finite face witness excludes heat-only replacement, not all interacting coarse actions. |

Monte Carlo/literature tables are labeled as such in the commit history;
they are not Lean certificates. No estimate is inferred from their numerical
values here. All the continuum/QFT/physical-mass/every-group obligations remain
open. The two main analytic producers remain window survival and an actual
all-vector changing-family contraction/comparison with a useful budget.

## Repoint to the stronger existing cost consumer

The preceding plan foregrounded the paired global budget. An already checked
direct-score route is stronger and avoids the conditional Jensen enlargement:

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepExactScoreCost.lean:218`,
  `exactScoreSignedBulk`, keeps the actual score square and signed remainder.
- Same file `:232`, `exactScoreSignedBulk_le_projected`, proves removal of
  the Jensen enlargement, with the source and signed remainder unchanged.
- Same file `:324`, `original_block_exact_score_cost_relative_tolerance`,
  already pays reciprocal correction, drift and reconstruction against the
  original surviving-source norm. Reuse it instead of reintroducing a global
  cap repeated at every link and angular plane.

## New finite cancellation and actual conditional-source join

Write R for the computed full-product Taylor remainder, h=1-w and

```
S(q,f) = R(q,q*f^2) - R(q*f,q*f),    eta = f-c.
S(q,eta) = S(q,f).
S(q,f) <= h^2*pairBudget(q,q*eta^2) - R(q*eta,q*eta).
```

The exact identity holds for EVERY nome/cutoff and supported q,f. It follows
from the same jump energy and unchanged angular derivatives, without source
stationarity, a gap, or a sign premise. The inequality requires the explicit
existing `sufficientCutoff w <= K` guard. The negative diagonal remainder is
retained. Its proved nonnegativity also yields a weaker mixed-only bound.

- `lean/YMGap/Continuum/SU2QuaternionCenteredSignedRemainder.lean:66`,
  `sourceEnergy_shifted`, retains the full product heat and both endpoint
  sources on any selected heat list; division is only by the fixed number 2.
- Same file `:98`, `weightedAngularEnergy_shifted`; `:106`,
  `signedRemainder_shifted`; `:131`,
  `signedRemainder_le_centered_mixed_minus_diagonal`; `:149`,
  `signedRemainder_le_centered_mixed`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCenteredMixedCost.lean:58`,
  `centeredMixedBulk`, keeps the original direct score and the favorable
  shifted diagonal remainder, with the same outer partition Z0.
- Same file `:72`, `exactScoreSignedBulk_le_centeredMixed`, proves the
  inequality on ACTUAL q and conditional ratio phi, with source support
  derived from the full spatial weight and terminal message.
- Same file `:99`, `original_block_centered_mixed_cost_relative_tolerance`,
  joins it to the COMPLETE original cleared cost at degree k+1:

```
A = g_(n+r+1),  b = T^(r+1)(g_n*psi),  q = projectedEndpointSource(A),
phi = blockConditionalRatio(n,r+1,psi,k+1), eta = phi-c,
Z0 = m(A^2), Z1 = m(A*T A), L = actual exactScoreAngularBudget.

Z1*m(b^2) - Z0*m(b*T b)
  <= Z0*(h*L + h^2*pairBudget(q,q*eta^2) - R(q*eta,q*eta))
     + (zeta+delta+epsilon)*Z1*m(b^2).
```

Only the remainder evaluation is shifted. At finite reciprocal degree, the
conditional ratio constructed from psi-c is NOT identified with phi-c.
No substitution of q^2 for the interacting density or identification of this
ONE-step Rayleigh cost with TWO-step squared-norm RG dissipation is made.

This extends the existing specialized centering API; it does not claim
centered control was absent. In particular,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:231`,
`normalizedRemainder_centered_square_bound`, already retains original variance
and signed source/angular-weight corrections. The mixed ceiling is an
alternative, not a proved improvement over that different corrected quantity.
Budget minimization under OWN centering, useful AF smallness and a uniform
changing-family modulus are NOT proved.

## Verification and next frontier

Two final serialized focused checks passed all 5+3 new printed gates within
{propext, Quot.sound}, emitting their local oleans. Independent read-only Sol
reviews confirmed cancellation, retained diagonal term, degree and partition
alignment. One monitored 20-GiB compiler, 12-GiB reserve, fresh capacity checks
before each launch, no competing workers and zero swap. No new holes, axioms,
classical input, frontier-field changes or raised heartbeats. Earlier failed
local elaboration is not proof evidence.

Final logs, SHA-256:

- `/private/tmp/ym-oct7-centered-signed-remainder.log`:
  `128982fd40a4b557e191db81867ef2b4a6c700be7104e1f4a7d65996d26e9edf`.
- `/private/tmp/ym-oct7-centered-mixed-cost.log`:
  `11208b43424ffc44f0882780d88e7e0e6cce21e18b6f57b489cd4ffb160aa69f`.

No full-root/tree build, full audit or hashed-baseline regeneration; CI stays
off. NEXT: estimate the COMBINED direct score, centered mixed contribution
and retained diagonal term in actual surviving-form units on the justified
family; construct the interacting coarse comparison, or a direct SAME-operator
estimate. Do not extend tolerance wrappers or require unnecessary full norm
coercivity. Independent AF survival, physical calibration/volume control,
SAME continuum OS/QFT structure, every group and Clay remain OPEN. Broad
canonical chart unchanged; no reprint.
