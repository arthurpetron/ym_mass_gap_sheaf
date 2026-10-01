# Mixed connected decay on the original bond completion

Date: 2026-10-01 UTC. Mixed connected correlations of ANY two completed
physical bond states now obey the original fixed-parameter gap estimate,
normalized by their own bond variances. Finite signed sources and separated
Wilson words are pinned to the original odd reflected joint functional.
This fills a same-object correlator consumer, not a continuum scaling input.

## Actual states and correlation

All new declarations are in
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSConnectedDecay.lean`.
Let H be the existing `BondCompletion`, B its `bondCompletedInner`,
Omega its existing vacuum, and q=`twoStepRate(hw0,hw1,width)`.
Nome 0<w<1 and width are fixed. The rate depends on both; it is NOT
uniform in width, coupling or physical spacing.

`connected`, line 64, uses the existing completed centered scalar through
the proved original-vector map `bondValue`. Write its value at lag k as

    M_k(X,Y) = B(X,T_k Y) - B(X,Omega)*B(Omega,Y).

`connected_positive_action`, line 74, proves this formula with the actual
bond positive-time action at EVERY strictly positive integer lag. Lag zero
is supplied by the original discrete identity, not an invented element of
the strictly positive numerical-time datatype.

## Checked mixed estimate

`connected_even_lag_sq_decay`, line 136, proves for EVERY n:Nat and
EVERY X,Y:H

    M_(2n)(X,Y)^2 <= (q^n*M_0(X,X))*(q^n*M_0(Y,Y)).

Thus the right side is q^(2n) times the two actual bond variances.
No square root or inverse of a variance is needed, including zero cases.
The bound is not on presentation coefficient norms or a bare Haar measure.

The argument centers the ORIGINAL vectors, uses exact time balance to
write M_(2n)=B(T_n cX,T_n cY), applies the existing completed
Cauchy--Schwarz inequality, and contracts each centered squared norm by
q^n. Nonnegative multiplication preserves both bounds. The existing inputs
are `centeredPart_time_pairing` in
`lean/YMGap/Continuum/BF4WilsonAllNomeUnitProjection.lean:231`,
`completedInner_cauchySchwarz` in
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedInner.lean:82`, and
`completed_iterated_norm_gap` in
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedGap.lean:214`.

## Original signed sources and words

`connected_source_pin`, line 110, identifies the complete correlation as

    bondForm(x,advance(k,y))
      - bondForm(x,unit)*bondForm(unit,y).

Each `bondForm` is the ORIGINAL normalized odd reflected joint limit,
defined in `lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealization.lean:63`.
The proof retains
both independently supplied signed expressions and both marginal means.
It advances the original finite source, not a substitute dynamics.

`connected_word_sq_decay` and `connected_word_source_pin`, lines 183
and 200, apply this to the vacuum-created one-step-separated Wilson words
already constructed in `BF4WilsonAllNomeBondOSSeparatedWords`. The time
buffer remains necessary; this is not an equal-time algebra homomorphism.

## Scope and verification

The new result extends the diagonal completed gap to a variance-normalized
mixed original correlation on EVERY bond class. It does not establish
spatial/spacing-uniform decay, nonzero continuum survival, physical time
or mass calibration, a canonical continuum OS root, full QFT axioms, or
every compact simple group. No canonical field or chart marker changes.

The final repaired focused check exited 0 and all eight printed gates are
exactly {propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide or noncomputable declaration. Independent Luna source review
confirmed the original norm, both means, signs and parameter scope.

Only main compiled, serialized by the monitored launcher with one worker,
20 GiB ceiling and 12 GiB OS reserve. Preflight found no competing compiler
or runner, 81 percent memory free and zero swap. Local notation/definition
rewrite errors were repaired before acceptance, without changed limits.
No full root build, tree audit or guard ran; root import registration was
not aggregate-root checking. CI remains manual-only.

Final log: `/tmp/ym-bond-connected-decay-repaired-20261001.log`.
SHA-256: `6b86948f759a55de9a542ecd22ae87acfee4c106a3fe6ec34eeed2bdee4e44fa`.

## Addendum: sharp complex mixed decay on the same physical completion

The missing complex phase inequality is now proved on the ORIGINAL literal
all-nome form, and its mixed-correlation consumer is checked. The previously
constructed complex physical completion and time are unchanged.

### Sharp inequality without a real zero decision

`orthogonal_pair_bessel`,
`lean/YMGap/Continuum/RationalOrthogonalPairBessel.lean:123`, proves

    B(x,y)^2 + B(x,z)^2 <= B(x,x)*B(y,y)

for an actual positive rational bilinear form, B(y,z)=0 and B(z,z)=B(y,y).
The computed `phaseVector` at `:51` is B(x,y)*y+B(x,z)*z. Write L for the
sum of the two pairing squares. Ordinary real Cauchy--Schwarz gives
L^2<=L*B(x,x)*B(y,y). The rational L<=0/0<L split covers the zero case
and otherwise cancels only the strictly positive rational L. No real norm
inverse, representative selection or analytic premise is introduced.

`finiteWindowComplex_cauchySchwarz`,
`lean/YMGap/Continuum/BF4WilsonAllNomeCauchySchwarz.lean:364`, applies this
to the direct sum of two copies of the ACTUAL finite reflected form
`finitePreInnerForm` (`:111`). Its `finitePairing` (`:40`) is the literal
originalWindowScalar with the original action, width and reflected sources.
The quarter-turn (y_im,-y_re) is orthogonal to y and has equal norm; its
pairing gives the conventional imaginary sign. Only the carrier-free
`directSumPreInnerForm` algebra is imported from the older module, never
the older physical form.

All four declarations in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexCauchySchwarz.lean` preserve
the sharp constant one:

- `common_complex_cauchySchwarz` at `:73` uses all eight original pairing
  convergences with all three joint stage indices equal.
- `intrinsic_complex_cauchySchwarz` at `:135` uses a shared chart containing
  all four original source radii, without changing literal width.
- `representative_complex_cauchySchwarz` at `:183` uses the existing
  `BF4WilsonAllNomeCompletedInner.pairingData` and its actual Cauchy limits.
- `inner_cauchySchwarz` at `:212` descends to the EXISTING complex Wilson
  completion by quotient induction, not choice of representatives.

### Exact completed covariance and actual consumer

The declarations below are in
`lean/YMGap/Continuum/BF4WilsonAllNomeComplexBondOSConnectedDecay.lean`.
`connected` at `:49` uses the four existing REAL physical covariances:

    Re M = C(x_re,y_re)+C(x_im,y_im),
    Im M = C(x_re,y_im)-C(x_im,y_re).

`connected_centered_pairing` at `:57` pins this to the original complex
pairing of centered x with original time applied to centered y.
`variance_pin` at `:65` identifies Var(x) with the actual centered complex
norm, hence the sum of the two original physical centered variances.
`variance_nonnegative` at `:69` proves its nonnegativity.

`connected_even_lag_modulus_sq_decay` at `:91` proves for EVERY n and every
pair of completed COMPLEX physical bond classes

    |M_(2n)(x,y)|^2 <= (q^n*Var(x))*(q^n*Var(y)).

Exact time balance gives M_(2n)=I(T_n cx,T_n cy); sharp complex
Cauchy--Schwarz and the existing `complex_iterated_norm_gap` then give
the result, without a factor-two loss. Zero variances and n=0 are included.
The SAME q=twoStepRate(hw0,hw1,width) depends on fixed nome and width.
There is no width/coupling/spacing-uniform rate assertion here.

`connected_source_pin` at `:121` preserves all four complete original
signed source covariances, each with its two marginal means. Each real
component's positive-integer operator bridge is the previously proved
`connected_positive_action`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSConnectedDecay.lean:74`.
The result does not assume a replacement dynamics or norm.

The PRIMARY signed scaling estimate, nontrivial continuum survival,
physical time/mass calibration, limiting OS/observable identification,
full QFT and every compact simple group remain OPEN. No canonical field,
guard, broad chart claim or mathematical target has changed.

### Focused verification and independent review

Four focused serialized checks exited zero, with 16 printed gates within
{propext, Quot.sound}; the phase-vector definition is axiom-free. These
include the two unchanged real gates in AllNomeCauchySchwarz, not 16 new
theorems. No sorry, new axiom, Classical dependency, native_decide or
noncomputable declaration was introduced. Sol independently checked the
literal finite form and eight-pairing joint/completion path; Luna checked
the physical variance, source signs and sharp consumer.

Main alone compiled with the monitored one-worker 20 GiB ceiling and
12 GiB OS reserve. Preflight found no competing compiler, 84 percent
pressure-free memory and zero swap. Initial elaboration/rewrite errors
were repaired before acceptance; no heartbeat or memory limit was raised.
The safe-build procedure confined checks to changed targets. Root imports
are registration only: no full root/tree build, broad audit or guard ran.
CI remains manual-only; the unchanged canonical chart was not printed.

Accepted logs and SHA-256:

- `/tmp/ym-orthogonal-pair-bessel-accepted-20261001.log`:
  `2ac2b84b030a1b855f4545424117c87514d3c4ff611c261fea4f7c8fd655299e`.
- `/tmp/ym-original-finite-complex-schwarz-repaired-20261001.log`:
  `7c80bdb1420aa0ec0d2a7cafafc9dd57b0523ca5bd3d0bdfafa047ebf1fd46a0`.
- `/tmp/ym-original-complex-schwarz-accepted-20261001.log`:
  `9f444b6be83d8216f9f3be655324bf59cc4d0f6c82ad2c79a100d45b8ac42f0d`.
- `/tmp/ym-complex-bond-connected-accepted-20261001.log`:
  `fd7985f88d3dc1317af5ed0ac3036fdaf4b2f22c543f68ec703232c1fbf057cc`.

### Read-only primary-frontier review, not another proved estimate

Sol's bounded review located the obstruction to automatically spending the
retained source square against interacting variance. Main checked the
actual definitions: `familyChannelObservableSquare`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyChannelRetainedSquare.lean:145`,
uses sum rho*H[b^2*f^2]. `padded_family_centered_channel_variance`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyPassiveCancellation.lean:324`,
instead identifies Z*Var with sum rho*H[b*(P b)*(f-m)^2] at the same global
odd mean. These are not the same insertion or source weight. Replacing
f by f-m introduces mean corrections, and replacing b^2 by b*(P b)
introduces weighted heat defects. The bare centered cross term is not
eliminated by the actual heat-paired centering identity. No reviewed
declaration supplies the useful source-specific sign or variance-relative
bound. This is a source/planning review, not a new Lean inequality or an
analytic certificate. The next action remains joint actual-source control,
not another exact expansion or assumed comparison bundle.
