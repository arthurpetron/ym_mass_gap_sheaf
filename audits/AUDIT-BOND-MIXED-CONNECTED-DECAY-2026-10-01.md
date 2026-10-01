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
