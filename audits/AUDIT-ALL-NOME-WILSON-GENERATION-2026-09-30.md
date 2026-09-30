# Explicit vacuum generation on the same all-nome Wilson completion

Date: 2026-09-30 UTC. Parent baseline: `82230de`.

## Proved increment and actual consumer

For every rational nome `0<w<1` and fixed literal width, every bounded
signed Wilson-window expression now has an explicit finite program in the
EXISTING vacuum, addition, rational scaling, completed time and time-zero
Wilson multiplication. Its evaluation equals the original embedded state.
For a supplied Cauchy representative and positive rational epsilon, the
compiler returns a program whose actual completed squared distance from
that representative's class is at most epsilon.

The proof first descends free source-polynomial identities through the
literal original joint limit. Comparing in the second pairing slot avoids
assuming that a source identity automatically survives reflection; form
symmetry then gives the first-slot equality used by the actual completion.
The finite compiler expands signed terms and sorts each word by time.
Successive nonnegative time advances and bounded loop insertions realize
that word exactly. Sampling the supplied Cauchy modulus finishes the
quantitative approximation, without selecting a quotient representative.

| Declaration | Source | Role |
| --- | --- | --- |
| `originalJoint_padded_congr` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowPins.lean:65` | Coefficient identity in the original normalized joint limit. |
| `embedWindow_eq_of_source_identity` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowPins.lean:136` | Descent to the SAME literal-width completion. |
| `completedMultiply_embedWindow` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowPins.lean:180` | Actual dense action of time-zero loop multiplication. |
| `completedTime_embedWindow` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowPins.lean:189` | Actual time advance with unchanged expression and enlarged radius. |
| `evaluate` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:48` | Uses only the existing all-nome completed operations. |
| `orderedProgram_pin`, `wordProgram_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:56`, `:74` | Exact chronological generation, then source-preserving sorting. |
| `compileWindow_pin`, `windowCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:103`, `:111` | Every bounded signed expression, with a Type-level program witness. |
| `intrinsicProgram_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:118` | Covers every dense intrinsic expression of this carrier. |
| `approximationProgram_bound`, `approximationCertificate` | `lean/YMGap/Continuum/BF4WilsonAllNomeWindowRealization.lean:126`, `:138` | Same-carrier quantitative generation using `X.modulus epsilon`. |

Only parameter-free syntax/compiler declarations from the older
`BF4WilsonChronologicalProgram` and `BF4WilsonWindowRealization` are reused.
Their small-nome evaluation and spatial-union pin theorems are NOT used.
The width, original action, completion, operators and distance are unchanged.

## Scope boundary and next analytic work

This supplies fixed-width Wilson-syntax vacuum generation, a supporting
J02 reconstruction result. It does not prove coverage of every gauge
observable or construct a continuum algebra. In particular it does not
inhabit `PositiveTimeOSRoot.stateEssentiallySurjective` in
`lean/YMGap/Continuum/CanonicalOSRoot.lean:296`, whose representatives and
supported observables belong to the canonical limit algebra. Cross-width
and spacing control, continuous physical time, full QFT, and Clay remain
open. No canonical chart claim or frontier field is changed.

Parallel source review retained a separate obstacle to the signed route:
`residualPolynomial` in
`lean/YMGap/Continuum/BF4ExactSlabSignedNeighborApproximation.lean:91`
does not truncate arbitrary input degree. Its `neighborValue` (`:97`) and
`signedNeighbor_error_bounds` (`:137`) control the actual polynomial
approximation, not a finite numerical matrix's omitted modes. The
`conditionalGenerator_square_polynomial_lower` consumer (`:189`) still
needs a useful lower estimate for that signed value relative to the same
energy. The normalized finite-feature domain and its remaining exterior
and full-degree obligations are recorded in
`audits/AUDIT-NORMALIZED-FEATURE-CERTIFICATE-DOMAIN-2026-09-30.md`.
No finite matrix calculation or new positive margin is claimed here.

## Verification

Both new modules passed focused serialized checks through
`scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20`, each
with its own `--check` source and `--check-output` olean. All 20 printed
gates were within `{propext, Quot.sound}`; `intrinsicProgram` is axiom-free.
The initial pins checks required namespace/notation and elaboration repairs;
the final checks completed in approximately 2.3 and 2.6 seconds.
No new sorry, axiom or analytic premise was added. No full-tree/root build,
audit or guard was run. No compiler remained live beyond its initial call,
so no manual polling was needed; automatic safety monitoring stayed active.

Sol implemented the literal source descent and operator pins; the main
agent implemented the finite-program and approximation consumer and ran
all checks. Luna independently reviewed carrier, premise and modulus scope.
