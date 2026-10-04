# Bidirectional checkpoint: nontrivial antipodal heat — 2026-10-04 UTC

PROGRESS after `aaf628e`: construct finite sign-quotient-compatible kinetic
data from paid original Haar inputs. The original SU(2) aggregate analytic
producer and the continuum/Clay theorem remain OPEN.

## Backward requirement and actual forward object

The every-group/global-form branch needs actual representations, Haar and
action data, not just group codes. The existing algebraic rational-point
quotient is `signLocatedQuotientPresentation`,
`lean/YMGap/RepTheory/RationalQuaternionSignQuotient.lean:128`; its exact
two-sign relation is `signCoset_iff`, same file:134. Neither constructs a
compact SO(3) or its Yang--Mills theory.

The new concrete analytic input is

    Hplus(x,y) = (H(x,y) + H(-x,y))/2.

`antipodalHeat`, `lean/YMGap/Continuum/SU2QuaternionAntipodalHeat.lean:187`,
uses the literal finite relative heat packet, not assumed mixing data.
All new declarations below are in that file:

| Declaration | Line | Exact result |
| --- | --- | --- |
| `supported` | 190 | Two original quaternion blocks only. |
| `sourceSign_invariant` | 198 | Independent source-sign invariance, coefficient equivalence. |
| `targetSign_invariant` | 207 | Independent target-sign invariance, coefficient equivalence. |
| `lower_marginal` | 251 | Unit lower Haar marginal against every supported original input. |
| `upper_marginal` | 270 | Unit upper Haar marginal against every supported original input. |
| `floorCertificate` | 300 | Actual square certificate for Hplus-headFloor(w), K>=headCutoff(w), 0<w<1. |
| `certificate` | 313 | Actual positive packet certificate with the same guard. |
| `antipodalMap` | 320 | Computed original partial-Haar integration against Hplus. |
| `map_mean` | 326 | SAME Haar mean preservation at every cutoff. |
| `map_square_contraction` | 332 | Ordinary Haar squared-norm cap one. |
| `map_centered_square_bound` | 340 | All supported centered inputs have the existing rate squaredHeatRate(w). |
| `evenMode_haar_norm` | 361 | The literal off-diagonal quadratic has Haar norm squared 1/24. |
| `evenMode_haar_mean_zero` | 365 | Its actual original Haar mean is zero. |
| `evenMode_map_mean_zero` | 368 | Its actual output mean is zero at every cutoff. |
| `evenMode_transmission` | 373 | At K>=2, arbitrary retained probes pair with the actual output by w^8. |
| `evenMode_map_norm` | 395 | ACTUAL output norm squared is (w^8)^2/24. |
| `evenMode_map_norm_positive` | 412 | This output norm is positive for w>0, K>=2. |

Sign transport preserves the inductive square certificates through ALL
retained Haar tests; it does not replace a carrier relation with a
coefficient identity. The output-norm proof tests the actual output against
itself and the explicit quadratic, rather than assuming a coefficientwise
eigenpin. The extra zero-mean pins identify a nonconstant mode.

The actual downstream consumers are `kernelMap_square_contraction`,
`lean/YMGap/Continuum/SU2QuaternionHaarMarkovContraction.lean:139`, and
`kernelMap_centered_square_bound`, same file:204. BOTH marginal premises
and the positivity/floor premises are now constructed for Hplus.
`squaredHeatRate`, `lean/YMGap/Continuum/SU2QuaternionRelativeHeatContraction.lean:83`,
is explicitly nome-dependent; no parameter-uniform physical gap is asserted.

## Same-object boundary

Hplus is a MODIFIED kinetic packet. Independent link-sign averaging of a
whole shared-link action product is not independent averaging of its face
factors. The existing `spatialWeight_starSign`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialVertexStar.lean:347`, concerns
vertex-star signs, not arbitrary independent link signs. This increment
does not descend the unchanged full SU(2) interacting action.

OPEN: compact/topological SO(3) realization and its Haar/action identification,
interacting transfer construction for that group and its analytic estimates,
every compact simple group's continuum construction, physical calibration,
canonical OS/full QFT, and the Clay theorem. No canonical frontier atom is
closed. No exact even-label expansion or arbitrary-parity map compiler is
claimed; independent endpoint invariance and a concrete surviving even mode
are the proved claims.

## Forward analytic review: not a new estimate

The second-order vacuum-cost theorem keeps incoming C and outgoing B:
`original_block_clearedRayleighCost_quadratic_vacuum_damping`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostCoercivity.lean:303`.
Normalizing retains their ratio; it does not construct the unpaid actual
aggregate budget in `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
No new smoothing, Riccati or assumed-budget wrapper is introduced.

The even-sector identity `paddedSquare_square_moment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareQuadraticHeat.lean:120`, uses q^2.
The required original variance pin `centered_source_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`,
uses q*Pq; `centeredMixedMoment`, same file:130, keeps the unpaid mismatch.
The already-checked `paddedSquare_energy_connected_overlap_cleared`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareConnectedDualOverlap.lean:284`,
does not supply the missing quantitative alignment lower bound. That
stronger initial-energy route remains optional, not necessary for survival.

## Backward probe choice: not a frontier weakening

`PositiveTimeOSRoot.probeObservable` and its norm, orthogonality and Rayleigh
fields, `lean/YMGap/Continuum/CanonicalOSRoot.lean:318`, do not prescribe a
growing square. `docs/outline.md:801` asks for a quantitative smeared local
gauge-invariant witness; the local-field/continuum pins remain necessary.

Already-constructed alternate finite probes are `familyExpression` and
`source_family_span`, `lean/YMGap/Continuum/BF4WilsonPlaquetteFamilySourcePin.lean:51`
and :92; `familyExcitation`,
`lean/YMGap/Continuum/BF4WilsonAllNomePlaquetteFamilyVariance.lean:147`;
and original temporal smearing `orbitSum`, `orbitSum_pairing`,
`orbitSum_orthogonal`, `lean/YMGap/Continuum/BF4WilsonAllNomeBilinearTime.lean:166`,
:195 and :215. Their fixed-parameter constructions are not new proofs here.
Do not make bare-square survival a universal Clay prerequisite or rebuild
these finite smearing wrappers. Quantitative localized-family scaling,
physical normalization, cross-spacing convergence and nonzero limiting
reflected correlations are still OPEN. The primary original signed-window
producer remains unpaid; no frontier statement is altered.

## Verification

The FINAL serialized focused check exited zero and printed **24 gates**,
all within `{propext, Quot.sound}`, with no errors or warnings. Independent
mathematical/source review passed the final source and its zero-mean pins.

- Source SHA-256: `e05b7613b13bc7f7d2790f152bbea921a70f710dd033489c24ca10eac66e5e38`.
- Accepted log: `/private/tmp/ym-antipodal-heat-20261004-4.log`.
- Log SHA-256: `0bba49fc0f401a6dd4e875908407002cf8d150e7a83c3df2cd87e444cc072d72`.

The first check was rejected for elaboration/support/notation errors;
the second passed 21 gates. Three explicit mean pins were then added;
their first check found a missing namespace open, corrected before the
final 24-gate check. No proof/resource inflation or analytic premise was
needed. Every launch had fresh process/swap/pressure inspection: no competing
compiler/runner, zero swap, 76--77% free. One worker, 20 GiB ceiling and
12 GiB reserve were preserved; each check finished in its initial call.

One new leaf and root import registration only. No full/root build, axiom
audit, guard, broad test/metric run, new sorry, axiom, frontier field,
classical input, CI change or resource increase. No paper-list/listing scan.
Exact canonical chart atoms are unchanged; no ASCII reprint.
