# Original boundary marginals: proof and next-consumer audit

Date: 2026-09-15 (local). Parent checkpoint: `50d0d9d`.
Parallel proof drafting and source review; serialized focused verification.

## Whole-project goal

Construct the nontrivial continuum quantum Yang--Mills theory and physical
positive mass gap required by Clay for every compact simple gauge group,
within the repository's constructive witness/modulus and axiom contracts.
All action, observable, OS, time and Hamiltonian identifications must concern
the same theory. This checkpoint proves finite SU(2) identities/estimates,
not continuum existence or a physical mass gap.

## New original-boundary identity

Write H for the original product quaternion Haar functional, L and R for
the complete original lower and reflected-upper heat-dressed observables,
and I for the actual crossing relative heat product. The proved reduction is

`original signed bilinear = H(L * I * R) = H(L_marginal * I * R_marginal)`.

The schedules integrate only each side's nonboundary link blocks. Every
other factor is proved independent before each Fubini step. Coordinates
are never renumbered; boundary locality and support are proved for the
residual polynomials. Shared boundary links need not be independent.

| Declaration | Source | Content |
|---|---|---|
| `quaternionHaarMono_eq_finiteProductHaarMono` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:50` | Same original moments, including out-of-carrier convention. |
| `quaternionHaar_eq_finiteProductHaar` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:59` | Functional bridge for arbitrary polynomials. |
| `quaternionHaar_polyMul_eq_after_integratingBlocks` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:77` | Exact spectator integration for an explicit in-range schedule. |
| `integrateBlocks_supported` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:93` | Same carrier support. |
| `integrateBlocks_local` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:134` | Removes all selected dependencies, preserving other locality restrictions. |
| `quaternionHaar_polyMul_eq_after_integratingBlocks_of_local` | `lean/YMGap/Continuum/SU2QuaternionOriginalHaarBlockMarginal.lean:173` | Original-Haar consumer of actual block-locality proofs. |
| `boundaryLinks` | `lean/YMGap/Continuum/BF4ExactSlabCrossingBoundary.lean:54` | Actual lower spatial crossing links and their literal reflections. |
| `relativeInterface_local` | `lean/YMGap/Continuum/BF4ExactSlabCrossingBoundary.lean:122` | All crossing heat factors depend only on that boundary. |
| `interface_relative_pin` | `lean/YMGap/Continuum/BF4ExactSlabCrossingBoundary.lean:134` | Existing Gram interface equals the actual relative-word interface under every Haar insertion. |
| `exact_bilinear_eq_relativeHaar` | `lean/YMGap/Continuum/BF4ExactSlabCrossingBoundary.lean:139` | SAME original signed form with both complete observables. |
| `interiorSchedule`, `mem_interiorSchedule` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:52`, `:57` | Computed schedule and exact membership characterization. |
| `lowerMarginal`, `upperMarginal` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:63`, `:66` | Explicit residual polynomials. |
| `lowerMarginal_local`, `upperMarginal_local` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:82`, `:86` | Boundary locality of both residuals. |
| `lowerMarginal_supported`, `upperMarginal_supported` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:90`, `:94` | Original carrier support of both residuals. |
| `exact_bilinear_eq_boundaryHaar` | `lean/YMGap/Continuum/BF4ExactSlabBoundaryMarginal.lean:100` | The displayed original-action marginal identity, w>=0, every finite cutoff and odd extent, arbitrary signed coefficient functions. |

These are unnormalized finite identities. No positive floor, mixing
coefficient, original-observable preimage or time-composition premise is
silently supplied. The signed observables are not asserted pointwise positive.

## Independent all-nome background consumer

For rational 0<w<1 and K>=headCutoff(w), the new declarations in
`lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean` give:

| Declaration | Source | Content |
|---|---|---|
| `lowerCertificate` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean:42` | Original lower spectator product. |
| `upperCertificate` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean:47` | Literal reflected upper spectator product. |
| `backgroundCertificate` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean:54` | Existing full positive presentation, retaining spatial spectators. |
| `background_weighted_bound` | `lean/YMGap/Continuum/BF4ExactSlabAllNomeBulkProbeBackground.lean:63` | Absolute signed-insertion integral <= supplied interval radius times the SAME original backgroundMass. |

The old small-nome statements are preserved. This removes their positivity
restriction at the explicit late cutoff, not collar error smallness:
`productErrorInterval`,
`lean/YMGap/Continuum/BF4ExactSlabBulkProbeCollarInterval.lean:88`, still
requires its distinct perturbative hypotheses. There is no common positive
all-nome floor or volume-uniform contraction claimed here.

## Next-consumer review: gluing and original observable realization

**Subsequent route refinement:** `audits/AUDIT-ALL-NOME-OS-TESTS.md`
records the existing centered even-slab action split/mixed pairing and the
direct all-nome covariance consumer. New adjacent-kernel/time composition
is not a prerequisite for that correlation route. The missing declarations
below concern a proposed boundary-kernel route, not a proof that all routes
must pass through it. All-nome original dual-test boundedness and original
cutoff-limit site positivity are now proved in the newer checkpoint.

The new residual is admissible as an ordinary polynomial insertion:
`expectation`, `lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:72`,
accepts RatPoly. `numerator_pin`,
`lean/YMGap/Continuum/BF4ExactSlabCoordinateAction.lean:130`, transports a
supported polynomial into a larger carrier under the embedded source face
set `keptIds`. It does NOT identify that law with the full larger action.
`full_action_split` in the same module at line 82 explicitly retains the
complementary heat product.

A constructed original OS-observable preimage for the new marginal is
**NOT FOUND** in the reviewed all-extent observable/recoding, plaquette
expression, coordinate inclusion/action, time embedding, thermodynamic time
and slab-kernel composition modules. The relevant existing data types are:

- `BoundaryObservable`, `lean/YMGap/Continuum/BF4ExactSlabAllExtentFiniteBoundaryObservable.lean:45`:
  finite face-label coefficients.
- `lowerObservable`, `lean/YMGap/Continuum/BF4ExactSlabAllExtentObservableHaarForm.lean:87`:
  their heat-dressed polynomial image.
- `PlaquetteExpression`, `lean/YMGap/Continuum/BF4ExactSlabPlaquetteObservableAlgebra.lean:49`:
  individual plaquette-character expression algebra.
- `Presentation`, `lean/YMGap/Continuum/BF4ExactSlabThermodynamicPresentation.lean:37`:
  a packaged expression, not arbitrary RatPoly.

Existing `sameTranslate_comp`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicTimeAlgebra.lean:43`, and
`completedTime_embedPresentation`, `completedTime_comp`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedTime.lean:60`, `:75`,
act on those already-constructed observables/completions. They do not pin
the new marginal pairing to adjacent finite-region composition.

An original-action adjacent-region gluing/time pin for this marginal is
**NOT FOUND** in that search scope. The required next identification must
retain the complementary action and account for the shared spatial slice.
Increasing `centralExtent` (`lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:734`)
also changes the common box extent used by `boundaryCompleteSlabPlaquettes`
in that module at line 169; it is not by itself fixed-spatial-volume time
extension. A preimage is necessary only if this route consumes the marginal
as an original state; a sufficient proved original-norm/quotient/intertwining
alternative remains allowed. Neither alternative is provided here.

Separately, the connected insertion consumer `insertion_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:86`, still
requires the actual distance-decaying determinant bound with both partitions.
The new exact identity and positive background estimate do not construct it.
Physical-scale control, continuum QFT, nontriviality and all compact simple
groups remain open.

## Verification and parallelism

The background proof and original-Haar block-marginal proof were drafted
independently, alongside a read-only existing-consumer review. The parent
proved the actual crossing locality and integrated original-bilinear consumer.
Only the parent launched Lean checks, serialized with one worker and 20 GiB
ceiling after process/swap preflights. Seven focused launches included three
syntax/namespace/implicit-argument correction reruns; final thirty public
gates (4+6+11+9) use only {propext, Quot.sound}. No raised limits or dependency
rebuild; no old theorem, frontier field, axiom or literal hole changed.
An independent read-only semantic review found no omitted action factor or
unsupported original-state/time claim in the two boundary modules. All four
own artifacts and their direct imports were fresh at the final source check.

Final log SHA-256 values:

- `/tmp/ym-all-nome-bulk-background.log`:
  `a37f003bcff7f84b8103464195ff6b434a77b78aa933687b263c1689dd296ad1`.
- `/tmp/ym-original-crossing-boundary.log`:
  `64864b06109fbd92331e345f3bbae81575adb7f913a72bf7768ea63d648cf4c8`.
- `/tmp/ym-original-haar-block-marginal.log`:
  `ec9208a8c5e49e36fbd0370f2a247ff9371a9f90d70b686fd555e7c6e46a98c7`.
- `/tmp/ym-original-boundary-marginal.log`:
  `b3e40dff912d48b99f4217653637761ed0b4db890fced33c694de01a4eebf286`.

Four semantic-root imports added. Root/full-tree build and full audit were
not run. CI remains manual-only. Goal remains active; no Clay-facing
canonical atom is declared closed by this checkpoint.
