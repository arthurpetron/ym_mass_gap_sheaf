# Same-weight multi-affine relative energy

Date: 2026-09-30 UTC. Classification: PROGRESS. Clay target OPEN.

## Changed viewpoint and proved result

Instead of rebuilding an incident/nonincident plaquette decomposition after
each derivative, split the polynomial by its literal degree in the selected
quaternion block. For degree at most one, write p=f+r, with f homogeneous of
degree one and r independent of that block. Choose predictor q=-r in the
existing relative Ward energy estimate. Its prediction error is exactly p,
and the angular derivative of r is zero. Thus

    H[W*Gamma_head(p)] <= M(C)*H[W*p^2],  M(C)=24+36*C^2.

Differentiation at another block preserves the head degree ceiling. Apply
the preceding bound to all six other-block derivatives, sum exactly, then
apply the bound to that block after its explicit head swap. The checked
result is

    H[W*S2_head,b(p)] <= M(C)*M(D)*H[W*p^2].

The two relative certificates refer to the SAME W in two explicit coordinate
frames. Neither a product probability law nor a local source replaces the
original weight or whole polynomial. C and D remain explicit inputs, so this
does not assert coupling independence. The second block is required to be
in range and different from the head.

## Declaration map

- `QuaternionHaarHeadAffineSplit.headAffine_split`,
  `lean/YMGap/Continuum/QuaternionHaarHeadAffineSplit.lean:83`: exact
  coefficient equality with computable filtered term lists. The constant
  and linear sectors retain support and have exact degree zero and one.
- `QuaternionHaarAffineRelativeEnergy.angular_energy_le_square`,
  `lean/YMGap/Continuum/QuaternionHaarAffineRelativeEnergy.lean:65`:
  original relative energy of every supported head-affine polynomial.
- `QuaternionHaarDegreeBoundReindex.degreeLE_reindex`,
  `lean/YMGap/Continuum/QuaternionHaarDegreeBoundReindex.lean:29`:
  degree ceilings under the explicit padded block involution.
- `QuaternionHaarMixedAngularDegreeBound.blockAngularDerivative_headDegreeLE_of_ne`,
  `lean/YMGap/Continuum/QuaternionHaarMixedAngularDegreeBound.lean:72`:
  the other-block derivative preserves the head ceiling, including literal
  zero-coefficient terms.
- `QuaternionHaarMixedRelativeEnergy.block_energy_le_square`,
  `lean/YMGap/Continuum/QuaternionHaarMixedRelativeEnergy.lean:46`, and
  `mixed_energy_le_block_energy` at :77: the two estimate steps.
- `QuaternionHaarMixedRelativeEnergy.mixed_energy_le_square`,
  `lean/YMGap/Continuum/QuaternionHaarMixedRelativeEnergy.lean:104`:
  the composed two-edge estimate above.
- `BF4ExactSlabSignedSourceEncoding.sourceSpan_full` and `affineSource_full`,
  `lean/YMGap/Continuum/BF4ExactSlabSignedSourceEncoding.lean:54`, :65:
  literal equalities between the full plaquette-indexed source with
  `incidentCoefficient extent c` and the Nat-indexed observable, also after
  arbitrary centering. This closes the previously noted encoding mismatch.

## Exact remaining consumer

Supply the source's two degree ceilings and the original action's two
relative certificates in the SAME exposed frame, then transport the actual
physical mixed-energy lower bound into that frame. The original-source
per-face estimate

    8*c_p^2*Z <= M(w)^2*H[W*(F-m)^2]

is still OPEN as a composed declaration. The generic two-Ward estimate and
source encoding are now supplied; no new analytic premise was introduced.
Summing the proposed per-face estimate still costs the number of faces.
A separate bounded-interference/dual-family argument is needed before
claiming a support-uniform signed Gram estimate.

Reviewed next implementation: use the two component inequalities separately.
Apply `mixed_energy_le_block_energy` in the A-link head chart, transport its
two energies back to the original frame, then use `block_energy_le_square`
with the B-link head swap. `BF4ExactSlabSelectedActionRelativeBound.selectedActionRelativeBound`,
`lean/YMGap/Continuum/BF4ExactSlabSelectedActionRelativeBound.lean:261`,
supplies each single-link frame at C(w)=6*relativeCap(w,2048). It does not
directly supply the sequentially swapped weight required by an immediate
application of `mixed_energy_le_square`; that mismatch must not be ignored.
`QuaternionHaarMixedAngularTransport.chain_mixedSquare`,
`lean/YMGap/Continuum/QuaternionHaarMixedAngularTransport.lean:149`,
already supplies the first frame's mixed-energy transport.

For the remaining source degree producer, assemble `BF4ExactSlabCenterCharge.face_degree`,
`lean/YMGap/Continuum/BF4ExactSlabCenterCharge.lean:73`, with
`BF4ExactSlabOddFaceIncidence.faceDegree_pin`,
`lean/YMGap/Continuum/BF4ExactSlabOddFaceIncidence.lean:48`, and the existing
`DegreeLE.add/smul/one` rules. This is a reviewed implementation plan, not
an assertion that the concrete composed declaration already exists.

SAME literal completed-carrier realization, controlled physical support,
nontrivial scaling survival, useful every-state decay, finite positive
physical mass, full continuum QFT and every compact simple group remain
OPEN. No canonical chart field changed; no chart is reprinted.

## Verification

Six focused checks, serialized through `scripts/safe_lean_build.py`, passed
18 printed public gates in {propext, Quot.sound}. One worker, 20 GiB hard
worker cap, 12 GiB OS reserve, dynamic safety telemetry. No increased memory
or heartbeat limit. Final logs:

- `/tmp/ym-head-affine-split-20260930.log`
- `/tmp/ym-affine-relative-energy-20260930.log`
- `/tmp/ym-degree-bound-reindex-20260930.log`
- `/tmp/ym-mixed-angular-degree-bound-20260930.log`
- `/tmp/ym-mixed-relative-energy-20260930.log`
- `/tmp/ym-signed-source-encoding-20260930.log`

No new sorry, axiom, classical premise, Rust oracle, changed frontier field,
or old sorry discharge. No full build/audit/guard or CI change. Sol supplied
the finite split, degree stability and source pin; Luna supplied the padded
degree transport. Root supplied the energy composition and all compilation.
Luna independently checked the same-weight/norm statement boundary; Sol
identified the separate-frame route above to avoid assuming an unsupplied
sequential-swap certificate.
