# All-label selection in the actual two-link heat packet

Date: 2026-09-21 UTC. WHOLE-PROJECT GOAL remains OPEN: constructive,
nontrivial continuum Yang--Mills on R^4 for every compact simple group,
with same-theory QFT axioms, isolated vacuum and finite positive physical
mass gap. These results concern the concrete SU(2) polynomial kernel.

## New proved content

Let p be any polynomial homogeneous and harmonic of degree d in its head
quaternion. Its coefficients may depend on all retained variables. For
every other label j, the polynomial-valued head Haar integral is zero:

    partialHaarHead(relativeSolid(j) * p) = 0,  j != d.

This is coefficient equality, before any tail integration. If d<j, use
the solid's harmonicity and degree; if j<d, interchange the factors and
use p's harmonicity. Both cases use the existing
`partialHaarHead_harmonic_lower_degree`,
`lean/YMGap/Continuum/SU2QuaternionHarmonicDegreeSelection.lean:106`.
No positivity or sign restriction on p is imposed.

The ordinary character in the actual packet is obtained using the existing
arbitrary-insertion two-radius equality `solid_character_pin`,
`lean/YMGap/Continuum/SU2QuaternionRelativeCharacterSelection.lean:157`.
With an arbitrary retained boundary r, the FULL finite packet consequently
satisfies

    H[(heat(w,K)*p)*lift(r)]
      = if d <= K then coeffW(w,d) * H[(character(d)*p)*lift(r)] else 0.

The same pairing has exact nome dependence

    H[(heat(w,K)*p)*lift(r)]
      = w^(d*(d+2)) * H[(heat(1,K)*p)*lift(r)].

Here `heat(1,K)` is the same finite packet at nome one. It is NOT identified
with the identity operator, a delta distribution, or a positive kernel.
This equality does not require or assert any of those properties.

## Source map and constructive specialization

| Declaration | Source | Content |
| --- | --- | --- |
| `evaluate_derivative` | `lean/YMGap/Continuum/SU2QuaternionTailEvaluationDifferential.lean:78` | Explicit tail evaluation commutes with a retained-coordinate derivative. |
| `evaluate_headLaplacian` | same file, line 96 | Retaining at least four coordinates commutes with the head Laplacian. |
| `evaluate_headDegree` | same file, line 122 | Syntactic homogeneous head degree is preserved. |
| `relativeSolid_harmonic` | `lean/YMGap/Continuum/SU2QuaternionRelativeHarmonicSelection.lean:55` | Actual specialized two-link solid has zero head Laplacian at every label. |
| `relativeSolid_harmonic_offDiagonal` | same file, line 65 | Every unequal-label partial Haar pairing with a homogeneous harmonic is zero. |
| `character_harmonic_boundary_zero` | same file, line 94 | Ordinary-character off-diagonal annihilation with an arbitrary retained boundary. |
| `heat_harmonic_diagonal` | same file, line 156 | The original complete packet reduces to its explicit diagonal pairing, with the cutoff guard. |
| `heat_harmonic_nome_scaling` | same file, line 206 | Exact Casimir power relative to the finite nome-one packet, without an identity-at-one premise. |

Specialization retains the first EIGHT coordinates. Only the two auxiliary
quaternions of the four-word identity are set to explicit units; the two
physical link variables are never fixed. The degree/harmonic proof uses
the evaluated solid itself as the homogeneous representative and then
`solid_specialization` (`SU2QuaternionRelativeCharacterSelection.lean:85`).
It does not incorrectly infer syntactic degree from coefficient equality.

The local kernel is literal: `heatAt_zero_one`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatPairGeometry.lean:45`,
identifies `heatAt 0 1` with `relativeHeat`. `heat_exposed` in that file
at line 89 supplies the existing whole-carrier block-reindexing pin. The
new results do not by themselves construct all-block product propagation.

## Remaining diagonal join

The all-degree diagonal reproducing identity and its exact dimension
normalization remain unproved here. This is smaller than the previous
all-label selection obligation: off-diagonal terms are now discharged.
The finite packet's remaining diagonal pairing is not an assumed field.

The actual substitution primitive is `translatedHeadPolynomial`,
`lean/YMGap/Continuum/SU2QuaternionPolynomialHaarTranslation.lean:387`;
its term construction keeps every original tail coefficient. Together
with `dropHeadPolynomial`,
`lean/YMGap/Continuum/SU2QuaternionHaarHeadConditionalProduct.lean:31`,
it specifies the intended diagonal test:

    dropHeadPolynomial
      (translatedHeadPolynomial (PolyQuaternion.coordinateVariable 1) p).

That expression is a target for a future theorem, not a proved reproduction
formula. Padding-sensitive monomial equality must be respected: the solid
specialization retains fixed-length zero padding, whereas the substitution
can have shorter exponent lists. Use an explicitly padded target or a
proved prefix/Haar-carrier equality, not an unjustified raw coefficient
equality. No new interface assumes this missing result.

The original terminal-source fringe reduction is already supplied by
`energy_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveEnergy.lean:129`,
and its marginal identities; do not rebuild that detour. After diagonal
reproduction, the actual product map, finite cutoff control and weighted
finite-time comparison still must be joined. In particular, the polynomial
degree of the full source V_K*g_K*f changes with K: a result for one fixed
harmonic p is not uniform control of that changing family.

No spatial/spacing estimate, small SAME-variance one-step rate, continuum
survival, physical calibration, full QFT or other-group realization is
proved. No canonical field, analytic premise, hole or axiom was changed.

## Verification and division of work

The two focused checks passed eight printed gates within
`{propext, Quot.sound}`. The dependency-complete target
`+YMGap.Continuum.SU2QuaternionRelativeHarmonicSelection:olean` also passed.
Final logs contain no errors, warnings or `sorryAx`. Checks were serialized
through the safe launcher with one capped 20 GiB worker. No full-root build,
full-tree audit or guard was run; automatic CI remains disabled.

Logs: `/tmp/ym-gap-tail-evaluation-differential-check.log`,
`/tmp/ym-gap-relative-harmonic-selection-check.log`, and
`/tmp/ym-gap-relative-harmonic-selection-build.log`.

Sol supplied the bounded differential-specialization draft, independently
reviewed the off-diagonal/packet argument (PASS), and inventoried the
diagonal substitution APIs. Main supplied the two-order harmonic argument,
actual packet and nome identities, integration fixes and serialized checks.
