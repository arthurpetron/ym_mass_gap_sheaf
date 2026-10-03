# Original conditional regression and surviving-norm drift payment

Whole-project goal: constructive, Mathlib-free continuum Yang--Mills on R^4
for every compact simple group, with nontrivial SAME-theory QFT, isolated
vacuum and finite positive physical mass gap. The Clay problem remains OPEN.

## The new analytic payment

Retain the original interacting T=P_w M_V and ell(p)=H[V*p]. For arbitrary
supported signed psi and depth n+t>=1, use the EXISTING constructed objects

    A=g_(n+t), b=T^t(g_n*psi), phi_k=G_k*b,
    Z1=ell(A*T A), B=ell(b^2).

The actual positive-window multiplier certificate proves

    ell(A^2*phi_k^2) <= B.

This now joins the existing terminal drift estimate, rather than assuming
that a drift bound on a different test norm is a surviving-norm bound:

    abs(boundaryDrift(A,phi_k)) <= eta_(n+t-1)*Z1*B,
    eta_s=kappa(w,width)*mixRate(w,width)^s,
    kappa=(kineticCap/kineticFloor)^2.

No inverse of A or B is used. Zero B, signed psi, and every reciprocal
degree k are included. The norm, source, center, transfer, original spatial
action and both partitions are unchanged.

blockConditionalDriftDepthCutoff(w,width,epsilon) is computed with the
existing geometricCutoff(mixRate,kappa,epsilon). At every depth s above
that onset, the same drift is bounded by epsilon*Z1*B. The onset has NO
heat cutoff K, reciprocal degree k, source or amplitude parameter; it is
uniform in K>=headCutoff(w) and all k at FIXED w,width. It depends on w
and width and is NOT a uniform modulus along a changing scaling family.

The supporting input declarations are multiplierSquareCertificate,
`lean/YMGap/Continuum/QuaternionHaarPositiveWindowInverse.lean:186`, and
boundaryDrift_terminal_abs_le,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:271`.
The explicit eta/kappa definitions are comparisonEta at
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:94`
and comparisonKappa at :81. geometricCutoff/geometric_bound are at
`lean/YMGap/Continuum/PositiveContractionResidual.lean:119` / :126.

## Complete reconstruction in the SAME relative currency

The actual terminal floor/cap also eliminates the source-dependent error
coefficient without inverting a terminal mass or partition. Set

    F=kineticFloor, U=kineticCap, m=ell(g_(n+t-1)),
    a=ell(A), E=ell(1), C=transferWeightedCap=U*E.

Actual positive certificates give three inequalities:

    Z0 <= U*m*a, F*m*E <= a, F*a^2 <= Z1.

Multiplication and reordering yield F^2*(Z0*C)<=U^2*Z1. Cancelling only
the FIXED positive kinetic floor gives Z0*C<=kappa*Z1. Consequently

    ErrorCoefficient=2*(Z1+Z0*C)*B <= 2*(1+kappa)*Z1*B.

The constructed blockEnergyRelativeErrorCutoff(w,width,epsilon) is
geometricCutoff(rho,2*(1+kappa),epsilon). For every k above this onset,
the COMPLETE error budget rho^k*ErrorCoefficient is <=epsilon*Z1*B,
as is the absolute error between D and the exact energy-plus-drift split.
The onset has no K, depth, source, source degree, partition or norm-floor
parameter. Zero B and signed psi remain included. This is fixed-nome/width
relative reconstruction, NOT a scaling-uniform bound or a signed-bulk
estimate. Its kappa and rho depend explicitly on w,width.

Inputs: blockWindowCertificates,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:103`;
weightedMass_product_floor,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:78`;
terminalMessage_certificate at :126; transferStepLowerCertificate,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSandwich.lean:197`;
transferWeightedCap,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferWeightedBound.lean:54`;
blockConditionalRatio_energy_error_abs_le,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalEnergy.lean:302`.

## Actual forward/backward cost consumer

For the actual last step t=r+1, retain Z0=ell(A^2) and the COMPLETE cost

    D=Z1*B-Z0*ell(b*T b).

The previous signed ceiling remains available with its favorable drift.
An alternative now pays ONLY the drift; it retains the signed Taylor
difference and the same actual projected angular budget:

    Bulk_k=Z0*((1-w)*LastStepAngularBudget+Rmixed-Rdiagonal),
    D <= Bulk_k + eta_(n+r)*Z1*B + rho^k*ErrorCoefficient.

At the two independently computed depth/degree onsets, this gives

    D <= Bulk_k + delta*Z1*B + epsilon.

That absolute-degree-onset variant remains available. The stronger actual
relative reconstruction above now gives, at the TWO fixed-parameter,
source/cutoff-independent depth and degree onsets,

    D <= Bulk_k + delta*Z1*B + epsilon*Z1*B.

Both tolerances are in the SAME surviving-norm currency; neither is
asserted family-uniform. No negative Taylor remainder is discarded, and
no relative Bulk_k estimate is supplied as a new hypothesis.

The next missing estimate is the useful ORIGINAL signed bulk comparison
against Z1*B on the literal OWN-centered growing square, together with
controlled moduli on a justified changing nome/width/spacing family.
The exact finite-to-completed consumers remain
originalOwnBlockVariance_converges,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:136`,
and originalOwnBlockCost_converges at :157. They hold at fixed nome,
width, scale and lag; they do not themselves give changing-family control.
The OWN source support is already constructed by ownPaddedSquareInterval,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRatio.lean:350`.

Thus real finite drift and reconstruction payments relative to the SAME
surviving norm are now proved, not merely assumed. The full useful
scaling-family cost, continuum survival, physical
calibration, reflected OS realization, full QFT and every-group claims
remain OPEN. No canonical frontier field is weakened or inhabited. The
exact displayed ASCII claims remain unchanged; no chart is reprinted.

## Regression diagnostic: why the paired square is not a lone variance

Use the SAME complete one-step weight W and signed incoming a,c. Write

    A=T a, b=T c, U=T(a^2), H=T(c^2), C=T(a*c), M=T1,
    Gram=U*H-C^2, E=U*b-A*C,
    J=I[W*(lift(A)*c-lift(b)*a)^2].

The exact division-free identity is

    U*J=A^2*Gram+E^2,
    U*lastStepScoreBudget=M*(A^2*Gram+E^2).

The full-slice Gram has a constructed positive certificate: two input
copies share the same surviving tail, the original positive weight copies
multiply a signed wedge square, and its partial Haar integral is twice
Gram. No positive source, stationary eigenmessage, normalizer inverse or
change of original weight is assumed. This proves Gram positivity, NOT
the upper bound needed by the surviving-norm consumer. The factor U is
not canceled and no additional global-U floor is imposed as a new
mandatory analytic obligation.

Original transfer linearity also proves exact c -> c+lambda*a invariance
of the paired residual and its leading score budget. This is not an
invariance theorem for the finite reciprocal correction or COMPLETE
signed cost. No OWN mean is silently changed.

A finite one-head Haar witness checks the potential omission:
W=1, a=2+x0, c=1, with an actual unit-floor certificate for a. Its moments
are A=2, b=1, U=17/4, H=1, C=2, Gram=1/4, E=1/4, E^2=1/16 and J=1/4.
Consequently U*J=17/16>A^2*Gram=1. It is J, not E^2, that is tested in
this inequality. This witness rules out silently discarding the regression
mismatch; it is not a BF4 terminal message or a Yang--Mills counterexample.

### Bounded next argument: reviewed mathematics, NOT a new proof

Independent Sol review identified a different, valid route for absorbing
the mismatch with the correct factor: M*Gram-J is the three-column Gram
determinant of (a,c,1). Its six-term three-copy antisymmetric wedge would
give an original shared-tail positive certificate and hence J<=M*Gram,
or lastStepScoreBudget<=M^2*Gram. This is NOT the invalid A^2/U omission.
The known positive-source witness is compatible: there M=1 and J=Gram.

That three-column producer is NOT yet constructed. Targeted search found
only the two-column gramDeterminantCertificate,
`lean/YMGap/Continuum/QuaternionHaarPolynomialGramDeterminant.lean:212`.
The existing copy/lift and partial-factorization primitives suffice for
the proposed three copies; a general determinant or reindex framework is
not a new required obligation. The finite three-copy product/expansion
pin and actual certificate are the next bounded candidate. Even after
that certificate, the useful SAME-norm comparison for M^2*Gram and its
family dependence would remain OPEN. No diagram node is changed by this
source/planning review.

## Declaration evidence

Names are in YMGap.Continuum and the namespace matching each module.

| Declaration | Source | Role |
|---|---|---|
| conditionalReplica_identity | `lean/YMGap/Continuum/SU2QuaternionMultiHeadConditionalGram.lean:96` | Original shared-tail two-copy integral equals twice Gram. |
| conditionalReplica_certificate | `lean/YMGap/Continuum/SU2QuaternionMultiHeadConditionalGram.lean:127` | Constructed positive weight times signed wedge square. |
| conditionalGram_certificate | `lean/YMGap/Continuum/SU2QuaternionMultiHeadConditionalGram.lean:153` | Actual retained-tail Gram certificate. |
| spectator_nonnegative | `lean/YMGap/Continuum/SU2QuaternionMultiHeadConditionalGram.lean:166` | Keeps arbitrary certified surrounding tail action. |
| lastStepRegressionGram_certificate | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRegression.lean:69` | Literal original transfer moments, signed inputs permitted. |
| lastStepScoreBudget_regression_pin | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRegression.lean:91` | Exact division-free decomposition, keeps M and mismatch. |
| lastStepPairedResidual_shift | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRegression.lean:124` | Actual transfer-linearity cancellation. |
| lastStepScoreBudget_shift | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepRegression.lean:150` | Leading budget only, not complete cost. |
| incoming_floor_certificate | `lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean:47` | Positive-source witness has explicit unit floor. |
| original_haar_moments | `lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean:74` | Exact original-Haar moments. |
| pairedSquare_exact | `lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean:86` | Literal J=1/4. |
| residual_square_exact | `lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean:89` | Distinct E^2=1/16. |
| regression_gram_mismatch | `lean/YMGap/Continuum/QuaternionHaarConditionalRegressionWitness.lean:94` | U*J>A^2*Gram. |
| blockConditionalRatio_surviving_square_le | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:81` | Constructed norm comparison, zero B included. |
| blockConditionalRatio_boundaryDrift_abs_le | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:126` | Drift relative to Z1*B for all k. |
| blockConditionalDriftDepthCutoff | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:152` | Fixed w,width,epsilon onset, no K/k/source. |
| blockConditionalRatio_boundaryDrift_tolerance | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:158` | Actual all-later-depth relative payment. |
| block_partition_cap_le_comparisonKappa | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:139` | Actual partition/cap comparison, cancels only fixed kinetic floor. |
| blockEnergyErrorCoefficient_relative_le | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:189` | Complete coefficient <=2*(1+kappa)*Z1*B. |
| blockEnergyRelativeErrorCutoff | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:217` | Fixed w,width,epsilon onset; no source/K/depth. |
| blockEnergyError_relative_budget_tolerance | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:224` | Direct scalar error budget for complete signed-cost consumer. |
| blockConditionalRatio_energy_error_relative_tolerance | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy.lean:264` | Absolute split error in SAME-norm currency. |
| originalBlockLastStepBulkBudget | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepDriftPaidCost.lean:47` | Literal signed Taylor/angular bulk data. |
| original_block_lastStep_driftPaid_cost_le | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepDriftPaidCost.lean:73` | Complete original cost with relative drift payment. |
| original_block_lastStep_driftPaid_cost_tolerance | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepDriftPaidCost.lean:97` | Separate depth and absolute-degree moduli, signs preserved. |
| original_block_lastStep_driftPaid_cost_relative_tolerance | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepDriftPaidCost.lean:124` | Both errors relative to Z1*B, no source/cutoff in onsets. |

## Verification boundary and review

Six focused targets were checked serially with scripts/safe_lean_build.py,
one worker, 20 GiB hard ceiling and 12 GiB reserve. Every launch had fresh
process/swap/memory-pressure preflight, with no competing worker and zero
swap. The 44 printed public gates are within {propext, Quot.sound}; two
witness polynomial definitions are axiom-free. Accepted logs have no
errors or warnings. Failed elaboration attempts are not acceptance evidence.

| Target | Accepted log | Public gates |
|---|---|---|
| SU2QuaternionMultiHeadConditionalGram | `/tmp/ym-multihead-conditional-gram-20261003-b.log` | 7 |
| BF4ExactSlabFixedSpatialLastStepRegression | `/tmp/ym-last-step-regression-20261003-a.log` | 6 |
| QuaternionHaarConditionalRegressionWitness | `/tmp/ym-conditional-regression-witness-20261003-b.log` | 18 |
| BF4ExactSlabFixedSpatialBlockConditionalDrift | `/tmp/ym-block-conditional-drift-20261003-a.log` | 4 |
| BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy | `/tmp/ym-block-conditional-relative-energy-20261003-d.log` | 5 |
| BF4ExactSlabFixedSpatialLastStepDriftPaidCost | `/tmp/ym-last-step-drift-paid-cost-20261003-b.log` | 4 |

Source SHA-256:

- SU2QuaternionMultiHeadConditionalGram:
  `0441f8cf8f4cafb35961fa563202a3a080526c2a5b0bbc7c09dee7a0655cb4be`
- BF4ExactSlabFixedSpatialLastStepRegression:
  `76703fb8645cb9ce13f5d6c1085145ec60c374eb1aae734554ccee95d7b09034`
- QuaternionHaarConditionalRegressionWitness:
  `cfb135518df6d7a752706f82d5fd8e40b940446a3e4b55d9e55173b3395b5a59`
- BF4ExactSlabFixedSpatialBlockConditionalDrift:
  `2a6b1f0bd32d5fe698e2ec54c9e47b4b68b3e28570c6fd8a09498465cacd8897`
- BF4ExactSlabFixedSpatialBlockConditionalRelativeEnergy:
  `e7a05cf02137c66f2d54ffea929843b5cdbe6303d34486213fbac9dde114ca16`
- BF4ExactSlabFixedSpatialLastStepDriftPaidCost:
  `71b31524a92fa6b6cb2294deca2caff28973cc09c1e75ce65b30ea0cc6b604a5`

Independent Sol source/log review passed the Gram producer and actual
regression pin. Independent Luna review passed the corrected Haar witness
and its accepted log, explicitly checking that J and E^2 are distinct.
Root reviewed the actual multiplier/drift join and the SAME-cost consumer.
Independent Luna review also passed the drift leaf and the earlier
three-gate paid-cost consumer. Final source/math and accepted-log review of
relative reconstruction and the four-gate consumer PASSED: the source
hashes above match the reviewed files, all nine printed gates are permitted,
and the same objects, zero cases, signed Taylor terms, onsets, live line
citations and fixed-parameter scope are preserved. No broader audit is inferred.
The relative leaf's first three failed checks are NOT accepted evidence.
Its public partition-band proof has a scoped two-million-heartbeat
elaboration limit; the hard memory/worker caps and safety telemetry were
unchanged. The successful check also corrects an explicit scalar congruence
argument order; it changes no mathematical hypothesis or conclusion.

No sorry/admit, new axiom, Classical, native_decide, noncomputable,
frontier field weakening, analytic hypothesis, axiom exception, or ledger
closure was added. Root imports are registration only; no full-root,
full-tree build, audit, guard, progress sweep or literature fetch was run.
