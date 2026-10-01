# Original heat mass comparison and physical bond quotient

Date: 2026-10-01 UTC. Two supplied-input steps are now proved. The original
slab partition absorbs additive constant kernel errors without an inverse
heat minimum, and decreasing one kinetic nome decreases its quadratic mass.
Independently, finite signed Wilson sources now have an explicit physical
bond-null quotient with an injective map into the existing completion and
computed dense approximants for witnessed time-sector states.

Neither result supplies the missing relative-energy estimate on a justified
physical scaling family. The continuum Yang--Mills and Clay target remain open.

## Floor free mass comparison

Fix the SAME supported endpoint source a and a retained spectator kernel W.
Write

    J   = H[W(x,y) a(x) a(y)],
    I_u = H[W(x,y) a(x) a(y) H_u,K(y_i x_i^(-1))].

Here W is positive semidefinite as a kernel. The existing representation
Gram theorem makes every relative-character quadratic nonnegative. Since
the heat coefficient is dim(j)*u^(j*(j+2)), coefficient monotonicity gives

    0 <= u <= w  ==>  I_u <= I_w.

The existing vacuum-channel comparison gives J<=I_w, since the spin-zero
coefficient is exactly one. This is spectral positivity, not a pointwise
heat minimum. The source may be signed for these two comparisons.

`SU2QuaternionHeatNomeComparison.prefix_nome_mono` proves the first
inequality; `constant_error_le` applies the second to a nonnegative constant
insertion. The underlying supplied declarations are
`SU2QuaternionProductHeatPositive.character_insertion_nonnegative`
(`lean/YMGap/Continuum/SU2QuaternionProductHeatPositive.lean:175`) and
`SU2QuaternionHeatFusionQuadratic.vacuum_le_prefix`
(`lean/YMGap/Continuum/SU2QuaternionHeatFusionQuadratic.lean:85`).

For a certified kernel-shape bound p<=c*H_u,K+e, with c,e>=0, multiplication
also needs positivity of W*a(x)*a(y). The new affine consumer requires that
certificate separately. It then proves

    H[W*a(x)*a(y)*p] <= c*I_u + e*J <= (c+e)*I_w.

The shape certificate is supplied, not manufactured. In particular, this
does not prove a quartic heat-kernel estimate. It proves that such an
estimate, if accompanied by a constant cutoff error, would not need to
pay an inverse minimum merely to absorb that error in this setting.

The initial source review suggested that erasing the selected heat factor
would require a floor. That was incorrect for the SAME-source PSD quadratic:
the already existing vacuum channel supplies exactly the needed comparison.
This correction has been independently reviewed and kernel-checked in the
original physical consumer below.

## The source and partition remain original

`BF4ExactSlabFixedSpatialHeatNomeComparison` takes
a=V_w*g_depth and W equal to the original product of all active kinetic
factors except the selected occurrence. No spectator, spatial action or
terminal source is recomputed at the comparison nome u.
`selectedMass_pin` proves I_w is exactly the existing oddMass.
`selectedMass_le_original` and `constant_error_le_original` have no
lower-cutoff guard: their PSD argument works at every finite cutoff.

`affine_original_bound` additionally constructs the certificate for the
complete positive insertion using the existing spatial, terminal and
spectator heat certificates. Its heat-head cutoff guard is therefore
explicit. It consumes the supplied shape certificate and bounds the actual
insertion by (c+e)*oddMass. The source, cutoff, width, depth, original nome,
comparison nome and selected slot all remain in the statement.

The comparison u=w*w is available in the generic theorem
`prefix_squared_nome_le`. It does not change the physical theory or set
the physical time scale. No logarithmic calibration is assumed.

## What remains analytic

The radial route still needs a positive-polynomial comparison for the
quartic selected-link displacement against a widened heat kernel, with a
useful explicit coefficient and cutoff error. It then needs the full-word
mixed-moment and SAME centered-variance comparison; the mass comparison
alone supplies none of these. The combined signed source-response route
remains available and is not replaced by an assumed positive remainder.

The existing positive response detector is not a near-identity bound.
Its `uniformFloor` is explicitly detectorScale squared divided by
costCap*partitionScale
(`BF4ExactSlabFixedSpatialPlaquetteUniformResponse.uniformFloor`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteUniformResponse.lean:98`).
The existing theorem
`BF4ExactSlabFixedSpatialResponseWidthObstruction.uniformFloor_le_margin_power_square`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialResponseWidthObstruction.lean:85`)
bounds this computed witness by (1/32)^(2*width). This is not an upper bound
on the actual retained response. Repackaging that detector does not supply
the missing physical-spacing survival estimate.

## Explicit physical bond null quotient

`BF4WilsonAllNomeBondOSQuotient.nullSetoid` identifies finite signed sources
x,y exactly when the original physical bond form of x-y has zero norm.
The quotient `Observable` maps to the unchanged original completion by
the already constructed root_1 image. `state_injective` shows that this map
makes exactly those identifications, and `inner_ofSource` recovers the
actual original bond expectation, not an independently postulated form.

The literal original one-step advance descends as `forwardTime` and
intertwines the existing transfer. The source unit maps to the existing
vacuum. `approximationData` returns a quotient source and its error proof
as Type-level data for every supplied witnessed sector state and positive
rational error. `denseObservable_bound` gives an explicit approximation
schedule using the existing source-modulus construction.

The map deliberately lands in the original completion, not in the
witness-bearing sector datatype. Equal completion vectors need not have
equal Type-valued range witnesses, and no representative or witness is
selected from the quotient. The result is a dense physical source quotient,
not its separately constructed completion/isometry, not a time-zero
multiplier representation, and not the canonical continuum OS root.

## Declaration map

Paths in this table are under `lean/YMGap/Continuum/`. Namespaces are the
corresponding module basenames.

| Declaration | Module:line | Proved scope |
|---|---|---|
| `prefix_nome_mono` | `SU2QuaternionHeatNomeComparison.lean:67` | Same-source selected heat-nome order |
| `prefix_squared_nome_le` | `SU2QuaternionHeatNomeComparison.lean:85` | Squared nome comparison |
| `constant_error_le` | `SU2QuaternionHeatNomeComparison.lean:98` | Vacuum-channel error absorption |
| `affine_prefix_bound` | `SU2QuaternionHeatNomeComparison.lean:113` | Conditional on explicit kernel-shape certificate |
| `selectedMass_pin` | `BF4ExactSlabFixedSpatialHeatNomeComparison.lean:83` | Exact original odd partition |
| `selectedMass_le_original` | `BF4ExactSlabFixedSpatialHeatNomeComparison.lean:110` | One changed kinetic factor, original full source |
| `constant_error_le_original` | `BF4ExactSlabFixedSpatialHeatNomeComparison.lean:122` | No heat-minimum penalty |
| `affine_original_bound` | `BF4ExactSlabFixedSpatialHeatNomeComparison.lean:135` | Actual positive spatial and terminal insertion |
| `nullSetoid`, `Observable`, `state` | `BF4WilsonAllNomeBondOSQuotient.lean:43`, `:57`, `:64` | Physical null quotient and original image |
| `ofSource_eq_iff_bond_null`, `state_injective` | `BF4WilsonAllNomeBondOSQuotient.lean:73`, `:83` | Exact null relation and injectivity |
| `inner_ofSource`, `distance_ofSource` | `BF4WilsonAllNomeBondOSQuotient.lean:96`, `:101` | Physical pairing and squared distance |
| `state_forwardTime`, `state_vacuum` | `BF4WilsonAllNomeBondOSQuotient.lean:119`, `:126` | Original time and vacuum |
| `approximationData`, `denseObservable_bound` | `BF4WilsonAllNomeBondOSQuotient.lean:132`, `:145` | Computed dense source approximants |

## Verification

Three final focused serialized checks exited zero. All 21 printed gates
passed: one uses only propext, the other 20 use {propext, Quot.sound}.
No sorry, new axiom, classical shortcut, native_decide, witness erasure,
surrogate substitution or canonical frontier weakening was introduced.
Initial syntax, namespace and explicit-width issues were repaired before
the final checks. Only the main agent ran Lean; Sol agents supplied the
quotient construction and independent source/scope reviews.

Checks used the safe launcher with one worker, a 20 GiB worker ceiling,
12 GiB OS reserve and dynamic safety telemetry. Preflight found no competing
Lean, Lake, pytest or runner process; macOS reported 91% memory free. No
full root build or broad audit was run. The root import list, roadmap,
ledger and supporting-status notes were updated; the canonical chart and
frontier fields are unchanged.

Final local logs and SHA-256:

| Log | SHA-256 |
|---|---|
| `/tmp/ym-heat-nome-comparison-20261001.log` | `cc43f785c4381c194c746b784be8926d76b1bd770a9b7f30350d7522eaa6b620` |
| `/tmp/ym-original-heat-nome-comparison-20261001.log` | `452af42da01293eb8cf7936e62161cf2323e2d5bcf9141c68a4bdbd2c7b4c066` |
| `/tmp/ym-bond-os-quotient-20261001.log` | `86228ddf1c00b1a5269d6a6318c974aff394c4e97d02e5f90bc2b292fed7dd59` |
