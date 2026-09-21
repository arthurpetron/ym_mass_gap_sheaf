# All-label angular Casimir: proof and scope

Date: 2026-09-21 UTC. Whole-project goal: constructive continuum
Yang--Mills on R^4 for every compact simple group, with nontrivial
same-theory QFT structure, an isolated vacuum and a finite positive
physical Hamiltonian gap. That goal remains OPEN.

## Mathematical increment

Write `D_ij = x_i partial_j - x_j partial_i`, and let L be the sum of
`D_ij^2` over the six head-coordinate planes. The new proof gives

    L p = radius * Delta p - secondEulerSum p - 3 * Euler p.

For a head-homogeneous harmonic polynomial of degree n, this becomes

    L p = -n(n+2) p.

The equalities are arbitrary-insertion Haar-carrier equalities, not raw
list equality and not a spectral assertion about the interacting transfer.
Degree zero is included. No commutation of mixed partials is assumed:
both orders occur explicitly in the six-plane expansion and Euler sum.

## Causal source map

- `headEuler_derivative_of_blockDegree`,
  `lean/YMGap/Continuum/SU2QuaternionHeadDerivativeEuler.lean:38`,
  uses the existing active derivative to avoid assigning a false degree
  to raw zero-coefficient derivative terms. Coefficient equality then
  transports the degree-(n-1) Euler identity back to the raw derivative.
- `secondEulerSum_of_blockDegree`, same file at line 58, sums the four
  coordinate-weighted identities and supplies the exact `(n-1)n` factor.
- `angularLaplacian_euler`,
  `lean/YMGap/Continuum/QuaternionHaarAngularCasimir.lean:133`,
  proves the full six-plane identity by Leibniz expansion and a
  kernel-checked polynomial identity. Coordinate-derivative padding is
  handled through existing Haar-carrier equalities.
- `harmonic_angularLaplacian`, same file at line 175, combines the
  Euler identities with harmonicity and proves the coefficient `-n(n+2)`.
- The concrete inputs are
  `exposedSolidZonalCharacter_blockDegree`,
  `lean/YMGap/Continuum/SU2QuaternionSpinTwoConditionalHaar.lean:125`,
  and `laplacian_exposedSolidZonalCharacter_zero`,
  `lean/YMGap/Continuum/SU2QuaternionSolidZonalHarmonic.lean:907`.
  They cover every label and all four orientation booleans.
- The solid-to-ordinary pin is
  `exposedSolidZonalCharacter_eq_character_116`,
  `lean/YMGap/Continuum/SU2QuaternionSpinTwoConditionalHaar.lean:139`.
  It retains arbitrary insertion in the original 116-block Haar carrier.
  `angularDerivative_carrier`,
  `lean/YMGap/Continuum/QuaternionHaarAngularCarrier.lean:55`,
  allows differentiating that equality tangentially twice, then summing.
- `exposedSolid_angularCasimir` and `exposedCharacter_angularCasimir`,
  `lean/YMGap/Continuum/QuaternionHaarExposedHeatCasimir.lean:63` and
  `:79`, perform that concrete construction and transport. The general
  carrier-compatibility theorem is `angularLaplacian_carrier` at line 45.
- `exposedHeatPrefix_angularCasimir`, same file at line 219, preserves
  the original finite sum and every `coeffW w n`, giving

      L heatPrefix = sum_{n=0}^K coeffW(w,n) * (-n(n+2)) * character_n.

  This exact algebraic equality requires no positivity, strict-nome or
  late-cutoff guard. It does not identify a convolution semigroup.

## Parameter and object boundary

The general theorem permits any positive number of quaternion blocks; its
concrete ordinary-character consumer uses the existing 116-block exposed
word. The eigenvalue depends on the label. It is not a single eigenvalue
for a heat prefix containing several labels. The original coefficients are
`coeffW w n = dimQ n * qpow w (c4 n)` in `BondMovingStep.coeffW`,
`lean/YMGap/Continuum/BondMovingStep.lean:259`, and the integer polynomial
`c4 n = n*(n+2)` is defined by `RGTransport.c4`,
`lean/YMGap/Continuum/RGTransport.lean:196`.

This is SU(2)/quaternion algebra. It does not supply the compact-group
construction or analysis for every compact simple group. No beta,
spacing-uniform estimate, or physical time normalization is asserted.

## Still-open join

The finite original Dirichlet identity is `energy_identity`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialDirichletForm.lean:253`.
Its actual edge weight retains both endpoint factors `V*g`.
The completed consumer `centered_relative_energy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointTemporalEnergy.lean:128`,
still requires a small one-step energy bound relative to the SAME variance.

No original-product heat semigroup identity, interacting transfer-generator
identification, Duhamel/gradient-energy inequality, or useful scaling rate
is proved by the new local Casimir identity. Such an operator comparison
must preserve the action, endpoint weights, partition, signed observable,
and cutoff errors. General physical-face reindexing is not supplied by
the exposed-word theorem alone. No canonical field or analytic premise
has been changed, and no new hole or axiom has been introduced.

## Verification

All three modules have passed focused checks; their ten printed gates
(4 Euler, 2 general Casimir, 4 concrete consumer) lie within
`{propext, Quot.sound}`, with no error, warning, `sorryAx`, classical axiom
or compiler-trusting reduction in the final logs.
All checks use the monitored launcher and one capped 20 GiB worker.
No full-root build, full-tree audit or guard was run.
The dependency-complete consumer target
`+YMGap.Continuum.QuaternionHaarExposedHeatCasimir:olean` also passed;
build log: `/tmp/ym-gap-exposed-heat-casimir-build.log`.

Sol supplied the bounded Euler and concrete-character drafts. Main supplied
the six-plane identity, integrated the proofs, and serialized verification.
Sol's independent review of the general proof passed the signs, degree-zero
case and scope. Explicit function arguments removed elaboration timeouts
without increasing a resource limit. Root imports were added; automatic
GitHub CI remains disabled.

Direct-check logs:

- `/tmp/ym-gap-head-derivative-euler-final.log`
- `/tmp/ym-gap-angular-casimir-check.log`
- `/tmp/ym-gap-exposed-heat-casimir-check.log`
