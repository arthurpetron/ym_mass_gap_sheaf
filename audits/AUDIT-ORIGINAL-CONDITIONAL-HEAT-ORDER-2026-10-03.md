# Original conditional heat: generator, shared-output joins and finite order

## Result and unchanged target

PROGRESS after `8653af8bd3d1a7c5c021c9714a5bb9c4d1190628`:
four new modules prove the actual saturated head heat's literal formal nome
generator, mixed composition at the already-existing retained output, its
true saturated nome-one endpoint, and constructive interval monotonicity
for finite signed rational polynomials. No advertised order or endpoint
identity is supplied as a theorem premise.

The whole-project goal remains OPEN: a nontrivial continuum Yang--Mills
theory on R^4 for every compact simple gauge group, with the required
same-theory QFT axioms and a positive physical Hamiltonian mass gap.
Conditional reference variance, original signed-cost scaling control,
continuum survival and the physical/OS/QFT/every-group passages remain OPEN.
The canonical chart's exact displayed claims have not changed; no reprint.

## 1. Forward: actual formal nome generator

`lean/YMGap/Continuum/SU2QuaternionHeadHeatGenerator.lean`:

- `nomeHeatPolynomial` (`:54`) constructs finite pairs of literal QPoly
  powers and the original signed harmonic groups, including every spectator.
- `finiteNomeFlow` (`:59`) evaluates those actual coefficient polynomials.
- `formalNomeDerivative` (`:64`) evaluates their literal `QPoly.pderiv`.
  It is NOT defined using the angular Laplacian.
- `nome_power_generator` (`:97`) proves the cleared finite power rule,
  including exponent zero and nome zero, without a nome inverse.
- `finiteNomeFlow_original_pin` (`:123`) pins this flow to the original
  `headMap w K p` under EVERY Haar insertion, for supported p and the
  computed `inputCutoff tail p <= K`.
- `headMap_formal_nome_generator` (`:199`) proves
  `w * formalNomeDerivative == -angularLaplacian (headMap w K p)`
  on the same carrier, with the same source/support/saturation guards.

This is a finite formal generator identity. No physical Hamiltonian,
analytic derivative, positivity at nome one or conditional variance bound
is asserted.

## 2. Forward: direct composition and endpoint at the original output

Write C_u p for the existing `conditionalHeat u K p`: integrate the old
head x against the actual relative heat k_u(x,y), keeping the already
existing output y and spectators z. The input p(x,y,z) may depend on y.

`lean/YMGap/Continuum/SU2QuaternionConditionalHeatComposition.lean`:

- `conditionalHeat_carrier` (`:51`) transports source carrier equalities
  through this actual integration, with arbitrary surviving insertions.
- `conditionalHeat_harmonic_carrier` (`:58`) proves actual harmonic
  transmission to the existing y, with arbitrary y-dependent coefficients.
- `conditionalHeat_headMap_composition` (`:142`) proves
  `C_u(headMap v K p) == C_(u*v)(p)` at the SAME inclusive cutoff, for
  supported p and `0 < tail`. No saturation or positivity is assumed.

The proof uses actual harmonic reproduction at y. It never identifies a
fresh output with y by pulling back an arbitrary Haar-carrier equality.

`lean/YMGap/Continuum/SU2QuaternionConditionalHeatEndpoint.lean`:

- `substituteRetained_radius` (`:50`) is a coefficient-strength pin for
  the particular selected-radius substitution.
- `substituteRetained_radiusIter` (`:57`) transports every finite radial
  power of the actual mode coefficients.
- `substituteRetained_paddedInput` (`:90`) transports the finite padding
  through its explicit coordinate-prefix identity, retaining support.
- `conditionalHeat_one_endpoint` (`:140`) proves
  `C_1(p) == substituteRetained p` for supported p, `0 < tail`, and the
  computed `modeCutoff (tail+1) p <= K`.

This last identity is obtained by coefficient reassembly and explicit
retained-radius unit reduction. It is not a generic non-injective carrier
or positive-certificate substitution theorem, nor positivity of k_1.

## 3. Backward analytic leaf: rational signed-polynomial interval order

`lean/YMGap/Continuum/RationalPolynomialIntervalOrder.lean`:

- `powerEval` (`:47`) is the literal monomial expansion; `powerEval_horner`
  (`:65`) proves its pin to actual Horner evaluation.
- `primitiveIncrement` (`:52`) is the computed signed coefficient sum of
  exact monomial antiderivative increments, not an abstract integral.
- `coefficientBudget` (`:57`) retains absolute values of ALL coefficients;
  `coefficientBudget_nonnegative` (`:61`) proves its nonnegativity.
- `monomial_quadrature_error` (`:116`) proves error <= mesh on a supplied
  finite unit-interval grid from exact left/right monomial rectangles.
- `polynomial_quadrature_error` (`:160`) proves error <=
  `mesh * coefficientBudget p`, for arbitrary SIGNED p.
- `polynomialLeft_samples` (`:186`) proves the actual sample-sum identity.
- `intervalMesh` (`:204`) and `intervalNode` (`:206`) construct the explicit
  N+1-cell grid of the actual rational interval [a,b].
- `primitiveIncrement_nonnegative` (`:290`) proves nonnegativity of the
  exact primitive from pointwise nonnegativity of actual polynomial
  evaluation, for `0 <= a <= b <= 1`. The error is bounded by an explicit
  natural coefficient ceiling divided by N+1; rational Archimedean closure
  removes it. No integral-limit or mean-value axiom is used.
- `formal_derivative_increment` (`:362`) proves the finite fundamental-
  theorem identity for the LITERAL coefficient derivative:
  `primitiveIncrement 0 (pderiv p) a b == eval p b - eval p a`.
- `monotone_of_formal_derivative_nonnegative` (`:383`) produces endpoint
  order from the actual formal derivative's pointwise sign on [a,b].

Zero polynomials, equal endpoints and signed coefficients are included.
Independent mathematical review passed the advertised finite result.

## 4. Exact next join, NOT discharged

The direct shared-output composition and saturated endpoint are now proved.
The forward heat generator and backward polynomial order leaf are also proved.
They do not yet give the conditional angular variance inequality
`C_w(Q^2) - (C_w Q)^2 <= (1-w^2) * C_w(Gamma Q)`.

The proposed remaining interpolation contains negative powers: on
`w <= r <= 1`, use actual finite expressions
`F(r)=C_(w/r)((headMap r K Q)^2)` and
`G(r)=C_(w/r)(Gamma(headMap r K Q))`.
Their exact finite Laurent row representations, formal derivative laws,
positive-prefix/saturation transports and endpoint order are still required.
The candidate identities `r*F'=2G` and
`r*G'=2*C_(w/r)(Gamma2(headMap r K Q))` are NOT new checked declarations.

Clearing a denominator in a DERIVATIVE sign test does not justify applying
polynomial monotonicity to the ORIGINAL Laurent function. Multiplying the
function by r^E changes its derivative and its endpoint comparison. The
remaining Laurent-order producer must prove the original endpoint order.

Intermediate kernel positivity must use computed larger prefixes and
saturation for each strict intermediate nome. A fixed truncated kernel is
not assumed positive up to nome one; nome-one endpoints use the proved
particular reproduction. Certificate-level diagonal transport, if used,
still needs its own explicit construction and is not supplied by these
carrier identities. Preserve the original Q_K, all action/signed Taylor
terms, and SAME surviving norm in the later BF4/window-cost join.

## 5. Focused verification and reproducibility

Four serialized monitored checks passed. Each command used
`scripts/safe_lean_build.py --jobs 1 --reserve-gib 12
--check-worker-limit-gib 20 --status-seconds 300 --check ...
--check-output ...` with the corresponding source and `.olean` path.
Fresh capacity was checked before each launch. No full build, full axiom
audit, broad YMGapGuard run or CI change was made.

Accepted logs and SHA256:

| target | accepted log | log SHA256 |
| --- | --- | --- |
| HeadHeatGenerator | `/tmp/ym-head-heat-generator-20261003-1.log` | `7d31c02db4053e549de8354c5a8f0ab07b381c6d347237d5eea8f34554744e89` |
| ConditionalHeatComposition | `/tmp/ym-conditional-heat-composition-20261003-1.log` | `9c78f91357311edbb8516c314821d20509c70e979b74d3849a7c6d564494ad83` |
| ConditionalHeatEndpoint | `/tmp/ym-conditional-heat-endpoint-20261003-1.log` | `c2e2f1a8c553221b990f43a029fa962c7e13404d1e4186bfe993d6f857b7c67a` |
| RationalPolynomialIntervalOrder | `/tmp/ym-rational-polynomial-interval-order-20261003-4.log` | `31448b9faf0e835f3b24a3c3915a8a9a415eab2186f754915a8b5a31c778c1b3` |

All 28 public gates are within {propext, Quot.sound}: seven computed
IntervalOrder definitions have no axioms, its coefficient-budget positivity
uses propext only, and the remaining twenty gates print propext and Quot.sound.
There is no sorryAx or Classical.choice in the accepted gate output.
Static source search found no sorry, new axiom, Classical, native_decide or
resource-option escalation in the four new modules.

Exact accepted source SHA256:

| module under `lean/YMGap/Continuum/` | source SHA256 |
| --- | --- |
| `SU2QuaternionHeadHeatGenerator.lean` | `b06906c3de157249cd088a08d1611a72cd67becc788ec0b3d4326c0ca84c9992` |
| `SU2QuaternionConditionalHeatComposition.lean` | `b951ec3fcf4f57a35450aebf427724693c1232596318f95d388df06b7125c55c` |
| `SU2QuaternionConditionalHeatEndpoint.lean` | `2ee8063a6d95e8f135da7bb1fc170cd30209fe18bc2663233c0eac08adbc2802` |
| `RationalPolynomialIntervalOrder.lean` | `382b6e3dd9578847037c338e9fe07418df9df3475855c8ad8fe3d9d940275188` |

Root imports are registered only; the root module itself was not rebuilt.
The legacy progress script remains unexecuted because it invokes the broad
guard, outside the focused verification scope. No frontier bundle or Clay
obligation is claimed discharged by this increment.
