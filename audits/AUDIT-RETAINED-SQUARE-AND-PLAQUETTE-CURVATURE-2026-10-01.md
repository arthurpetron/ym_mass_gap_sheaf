# Retained source square and actual plaquette curvature

Date: 2026-10-01 UTC. The original quadratic correction now has a stronger
whole-family upper estimate with a computed nonnegative gain. Independently,
the curvature of one literal physical plaquette is evaluated exactly on the
full original Haar carrier. These are finite SU(2) results, not a physical
scaling rate or a continuum mass-gap theorem.

## Constructed Gram determinant and retained square

`QuaternionHaarPolynomialGramDeterminant.gramDeterminantCertificate`
(`lean/YMGap/Continuum/QuaternionHaarPolynomialGramDeterminant.lean:212`)
returns Type-level square data for

    (sum_i a_i^2)*(sum_i b_i^2) - (sum_i a_i*b_i)^2.

Its recursive Lagrange identity adds the squares
(a_head*b_i-b_head*a_i)^2. Polynomial variables may overlap; repeated list
entries are retained. Supportedness, not independence, is the premise.

In `lean/YMGap/Continuum/SU2QuaternionSecondOrderRetainedSquare.lean`,
`angularPairs`, line 50, lists all six original angular planes of each active
block, with multiplicity. `angularGramCertificate`, line 98, pins this
finite determinant to Gamma(q,q)*Gamma(f,f)-Gamma(q,f)^2.

`retainedSquareCertificate`, line 138, uses the SAME eigenpin Cf=12f and
the following integer-coefficient identity, with v=q*f, x=Gamma(q,f),
y=Gamma(q,q), g=Gamma(f,f), B=12v-2x and s=12v-3x:

    3*(B^2 + 2*y*g - 48*v^2) = 2*s^2 + 6*(y*g-x^2).

Both terms on the right have constructed certificates. Multiplication by
the explicit positive rational 1/3 supplies the target certificate; the
integer polynomial identity is kernel-checked by coefficient reflection.
No source inverse, stationarity or variance-comparison premise is used.
`retained_square_bound`, line 211, integrates it. Combining it with the
previous exact quadratic split, `sourceSecondMoment_le_retainedSquare`,
line 240, proves

    D2 <= -H[q^2*C Gamma(f,f)] - 48*H[(q*f)^2].

Here C is the original finite angular Casimir, not the physical Hamiltonian.
The full observable and its signed cross terms stay inside each expression.

## Whole original signed-family consumer

All declarations in this section are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyRetainedSquare.lean`.
`projectedObservableSquare`, line 71, is H[(q*f)^2] for the ORIGINAL
q=projectedEndpointSource(w,K,width,terminalMessage(w,K,width,n)).
`projectedObservableSquare_nonnegative`, line 75, constructs its sign from
supportedness. This raw Haar quantity is NOT the interacting variance.

`quadraticCoefficient_family_le_retained`, line 82, supplies the actual
`BF4ExactSlabFixedSpatialFamilyCasimir.spatialSpan_casimir` eigenpin and
all support inputs, for arbitrary signed coefficients and repeated faces.
`retainedVarianceCeiling`, line 107, changes only the D2 upper estimate.
`retainedVarianceCeiling_gain`, line 120, proves the exact equality

    retainedCeiling = previousCurvatureCeiling
                      - (h^2/2)*48*H[(q*f)^2]/Z,  h=1-w.

`retainedVarianceCeiling_le_curvature`, line 151, proves this payment is
nonnegative for supported f. It can vanish: no strict gain is asserted.
`secondOrderVarianceCeiling_family_le_retained`, line 177, bounds the
original second-order ceiling by this new one.
`padded_family_energy_le_retained`, line 200, feeds it into the EXISTING
whole-family energy/variance identity:

    E_original/Z_original <= 12*h*Var_original + retainedCeiling.

The projected source remains at depth n. Original oddMass, oddVariance and
its original mean remain. sourceFirstOrder, actual cubic and coordinatewise
cutoff payment, -h*angularWeightDefect and -h*completeWardResidual remain
signed or budgeted exactly as before. No alternate density or terminal-depth
substitution is made. All inputs to this finite consumer have producers.

## Exact literal plaquette geometry

In `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteCurvature.lean`,
for the literal f=characterPolynomial(plaquette(width,face).scalar,1):

- `plaquette_gamma`, line 129: Gamma_full(f,f) is carrier-equal to 4*(4-f^2).
- `plaquette_square_casimir`, line 279: C_full(f^2) is carrier-equal to
  32*(f^2-1).
- `plaquette_gamma_casimir`, line 382: C_full Gamma_full(f,f) is
  carrier-equal to -128*(f^2-1).

These are arbitrary-insertion Haar-carrier equalities, not bare integrals
or heat asymptotics. The original four-link selection is exposed as the
computable `fullRangePlaquetteSelection`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteSquare.lean:65`).
Its added `slots` field is proved from literal geometry. Its full-range
permutation retains EVERY original block; the remaining angular derivatives
vanish by spectator independence. No Haar or interacting spectator factor
is discarded. Public Casimir linearity lemmas have unchanged proof bodies
in `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyCasimir.lean:242`
(`activeCasimir_add`) and `:263` (`activeCasimir_smul`).

The final curvature mode is signed. The one-face identity does not evaluate
the cross terms of a whole signed family or give them a useful sign.

## Open analytic input and unchanged whole-project target

Useful control of the COMPLETE signed correction relative to SAME
interacting variance on a justified physical scaling family remains OPEN.
In particular H[(q*f)^2] is not identified with that centered variance;
the signed curvature, angular-weight and Ward terms and the changing-source
cubic/cutoff budgets still need a combined actual-source estimate. A proved
nonnegative finite gain does not establish its required scaling size.

Physical spatial/spacing-uniform decay, nonzero continuum survival, full
same-theory OS/QFT construction, physical mass calibration and every compact
simple group remain OPEN. No canonical frontier field, displayed node label,
status marker or chart layout changes. No unchanged ASCII chart was printed.

## Verification boundary

Six final focused file checks exited zero, passing all 24 printed gates
within {propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide or noncomputable declaration. Sol implemented physical
geometry and independently reviewed the retained-square signs and unchanged
original-law pins; Luna implemented the generic polynomial Gram producer.
Only main compiled. Namespace, syntax, rational-reflection and scalar
congruence repairs did not weaken the mathematical inputs.

Every check used the monitored launcher, one worker, 20 GiB ceiling,
12 GiB OS reserve and continuous dynamic safety telemetry. Preflight found
no competing Lean/Lake/test/runner process, 83 percent memory free and zero
swap. No worker/memory/reserve limits were raised. Root imports were
registered but not checked in aggregate. No full root/tree build, audit
or guard ran. GitHub CI remains manual-only. The documentation skill
preserved the finite/open distinction in the audit and live plan.

Accepted logs under `/tmp/`, SHA-256:

- `ym-plaquette-selection-slots-20261001.log`:
  `68dd9e7aa22c6548b348ce0570ae79097771bedaf450c7380d264cff6e5004b1`.
- `ym-active-casimir-linearity-public-20261001.log`:
  `d7f71ac0697ea3976219980ec30d00d9429095aaf571fb1454c641161a316731`.
- `ym-polynomial-gram-determinant-accepted-20261001.log`:
  `f62bbc69f07535fc833d8604b3def92c5b2afdff6c7d5805fef19fb3e9661414`.
- `ym-physical-plaquette-curvature-carrier-20261001.log`:
  `91f76f53cd61e01ccbf18bc11d6a79b60be86940227f801ebf55a68ca9b5f319`.
- `ym-second-order-retained-square-accepted-20261001.log`:
  `727ed5790db88ff4a5c24174ca9d6b2d4b8abf5f1d0c1ccf21759216fe4cae35`.
- `ym-family-retained-square-accepted-20261001.log`:
  `d0f42ca9a5c1c0c2049d1ab12e075c9da8fd9c4590d19e48ee32ef8e9203e978`.
