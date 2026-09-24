# Rational linear geometry on the SAME all-nome Wilson completion — 2026-09-24

## Outcome and scope

Baseline: `5b81e16`. Five narrow checks establish rational algebra, positive
definiteness, fixed-point separation, quantitative time-difference nonvanishing,
and finite signed time-filter pairing on
the existing literal-width all-nome Wilson completion. The result is partial
J02 evidence only: it is not full real Hilbert structure, OS/QFT structure,
scaling control, a continuum limit, or a physical mass statement.

No older face-span or small-nome carrier is substituted. The shared
`scalarTolerance` and `twoStepRate` declarations are reused only as scalar
data; they do not identify carriers or add analytic hypotheses.

## Verified same-carrier constructions

1. `BF4WilsonAllNomeLinear.distSq_sum`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:69`) and
   `BF4WilsonAllNomeLinear.distSq_smul`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:99`) prove the quadratic addition
   and exact rational-scaling bounds for the actual all-nome seminorm.
   `addition` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:115`) and
   `scalarContinuous` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:120`) feed the generic
   explicit-modulus completion maps, producing `completedAdd`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:132`), `completedSmul`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:135`), `completedZero`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:138`), `completedNeg`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:141`) and `completedSub`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:143`) on the existing
   `Completion`. The Cauchy moduli remain explicit in `addition_cauchy_modulus`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:146`) and
   `scalar_cauchy_modulus`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:151`). Dense embeddings
   are preserved exactly by `completedAdd_embed`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:174`),
   `completedSmul_embed` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:178`),
   `completedZero_embed` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:182`),
   `completedNeg_embed` (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:185`)
   and `completedSub_embed`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinear.lean:189`).

2. `BF4WilsonAllNomeLinearLaws` proves the rational vector laws on that same
   quotient: `completedAdd_assoc`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:35`),
   `completedAdd_comm`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:48`),
   `completedZero_add`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:58`) and
   `completedAdd_zero`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:71`); additive
   inverses are `completedNeg_add`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:74`) and
   `completedSub_self`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:89`). Scalar
   one/zero/multiplication, distributivity and congruence are `completedSmul_one`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:93`),
   `completedSmul_zero`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:102`),
   `completedSmul_mul`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:112`),
   `completedSmul_add`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:123`),
   `completedAdd_smul`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:136`) and
   `completedSmul_congr`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeLinearLaws.lean:148`). This is rational algebra only, as stated by
   the module contract; no real-scalar completion is claimed.

3. `BF4WilsonAllNomeGeometry.distSq_zero`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeGeometry.lean:45`) and
   `.completedInner_posdef`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeGeometry.lean:71`)
   connect the actual distance to the diagonal form and prove that zero
   completed norm is exactly equality with `embed (zero width)`. The
   `vacuumComplement_twoStep_fixed_eq_zero` corollary
   (`lean/YMGap/Continuum/BF4WilsonAllNomeGeometry.lean:80`) uses the
   existing universal completed two-step bound and
   `twoStepRate_lt_one` to show that a fixed orthogonal vector is zero. This is
   fixed nome/width geometry, not vacuum isolation or physical mass.

4. `BF4WilsonAllNomeBilinearTime` passes rational bilinearity through the
   actual pairing: `representativeInner_add_left`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:58`),
   `representativeInner_smul_left`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:69`),
   `completedInner_add_left` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:79`),
   `completedInner_add_right` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:85`),
   `completedInner_smul_left` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:90`)
   and `completedInner_smul_right` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:96`).
   It also proves time commutation with completed addition/scaling and subtraction
   via `completedTime_additive`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:134`),
   `completedTime_smul` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:142`)
   and `completedTime_sub`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:159`). `orbitSum`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:166`) and
   `responseSum` (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:170`)
   retain all signed coefficients, and `orbitSum_pairing`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:195`) expands both finite sums
   into the complete double correlator with every cross term. The finite sum
   remains in the strict orthogonal sector via `orbitSum_orthogonal`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:215`)
   and inherits the fixed-parameter two-step bound via
   `orbitSum_twoStep_form_gap`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:228`), without
   asserting that it is nonzero.

5. `BF4WilsonAllNomeTimeDifference.timeDifference_norm_lower`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:122`) proves
   the constructive inequality
   `(1-twoStepRate)^2 * B(x,x) ≤ B(x-T^2x,x-T^2x)` on the same orthogonal
   carrier. `differenceFloor`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:170`) and
   `positiveTimeDifferenceExcitation`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:192`) provide an
   actual positive squared-norm floor for the centered origin-plaquette time difference
   at every positive width; `differenceFloor_positive`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:174`) and the
   explicit plaquette consumer `plaquetteTimeDifference_norm_floor`
   (`lean/YMGap/Continuum/BF4WilsonAllNomeTimeDifference.lean:179`) complete
   that witness.
   This is a particular nonzero finite filter and does not establish A03
   scaling survival.

## Verification boundary

Five serialized narrow checks exited successfully. They printed 61 gates in
total, all within `{propext, Quot.sound}`; no full-root build or full-tree
audit was run.

| Leaf | Log | Printed gates |
|---|---|---:|
| `BF4WilsonAllNomeLinear` | `/tmp/ym-gap-wilson-all-nome-linear-check-2.log` | 18 |
| `BF4WilsonAllNomeLinearLaws` | `/tmp/ym-gap-wilson-all-nome-linear-laws-check-3.log` | 12 |
| `BF4WilsonAllNomeGeometry` | `/tmp/ym-gap-wilson-all-nome-geometry-check-2.log` | 3 |
| `BF4WilsonAllNomeBilinearTime` | `/tmp/ym-gap-wilson-all-nome-bilinear-time-check-1.log` | 20 |
| `BF4WilsonAllNomeTimeDifference` | `/tmp/ym-gap-wilson-all-nome-time-difference-check-3.log` | 8 |

The checks used one worker, the stated 2 GiB worker cap, default elaboration
limits and the unchanged 12 GiB reserve. Earlier namespace, `zero_add` and
scalar-distribution display issues were corrected before these logs. No source `sorry`, classical
axiom, new premise, carrier replacement, or axiom-gate regression is present.

## A03 boundary and remaining analytic gap

The constructions above make signed finite time combinations and their actual
same-carrier correlators available, but do not close A03. The exact original
odd-middle route proves `frame_centered_ward`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredWard.lean:138`),
retaining the signed `centeredLinearWardResidual`; its plaquette instance is
`plaquette_centered_ward`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredWard.lean:166`). The
source route separately proves the signed identity involving `energy` and
`sourceIncrementCost` in `padded_terminal_plaquette_young_channels`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungExplicit.lean:115`),
and bounds their sum in
`padded_terminal_plaquette_signed_geometric_budget`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceYoungGeometricBudget.lean:77`).

What is still unproved is the needed same-observable/marginal comparison
between those two routes: no declaration identifies or bounds the Ward
residual/angular term by the source-increment correction/energy with the
required useful sign and scale. Thus these exact signed identities do not supply
the missing useful energy-to-SAME-variance comparison or justified
changing-scale survival; independent plaquette variance floors are not being
disputed here.
This audit does not assume that a fixed-plaquette `O(1-w)` relative bound is
necessary or true.

Snapshot 13 records partial J02 evidence only. The canonical chart,
labels, layout, and proof markers remain unchanged; no goal node is closed or
silently narrowed.

The chart block is byte-identical to snapshot 12, with SHA256
`1201d45415516d6791135982068aba2bba935a0d972d25d931dee374e20df041`.
Three semantic-root imports are added; no full-root build, full-tree audit,
guard or broad progress suite was run. CI remains unchanged.
