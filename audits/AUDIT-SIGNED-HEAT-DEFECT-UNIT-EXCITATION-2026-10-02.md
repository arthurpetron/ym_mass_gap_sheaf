# Forward-backward join: original signed heat defect and unit excitation

## Checked forward result

On the original SU(2) fixed-spatial carrier, let P be its active product
heat, q=V*terminalMessage, f the literal padded dyadic fundamental Wilson
square, mu its OWN original odd-marginal mean, psi=f-mu, Z its original
positive partition and V_own its OWN variance. Set a=w^(12*side), s=1-a.
The new modules construct, rather than postulate,

    C=P(q*f)-a*(Pq)*f,
    G=H[q*psi*C].

Coefficient linearity proves the exact generic identity
E=s*S+s*mu*J-G. The original source-marginal pin gives J=0 and
S=Z*V_own. The actual original energy and its SAME normalization therefore
satisfy

    E=s*Z*V_own-G,
    E/Z=s*V_own-G/Z.

The generic algebra holds for arbitrary a without even a bare-observable
eigenpin. G is SIGNED and no favorable sign or useful estimate is proved.
The concrete guards are 0<w<1, headCutoff(w)<=K and side<width; there is
no separate K>=1 or K>=2 guard. No source independence, channel projection,
variance inverse, local-band estimate or angular-generator substitution
enters this identity. This does not identify finite product heat with an
angular Laplacian.

## Checked backward-side construction

The EXISTING centered dyadic excitation v has an explicit QCauchy norm
representative A and a positive rational starRatio(w) floor at each strict
nome. The existing clamped inverse-root construction returns a real scalar
b, with its own QCauchy data, satisfying b*(b*A)=1 for this ORIGINAL norm.
The new actual consumer sets u=b*v in the SAME completed vacuum complement.
It proves

    B(u,u)=1,  u != 0,
    B(u,T(lag)u)=b^2*originalConnectedCorrelator(lag).

The corresponding real response has constructed QCauchy data. Its old
geometric lower fraction r^lag is retained unchanged. This explicitly
renormalizes the observable; it is not a uniform unrenormalized variance
floor. It needs no new analytic premise or selected norm representative.
It deliberately uses a witnessed inverse square root, unlike the energy
identity above.

Normalization removes an unrenormalized scale-uniform norm-floor demand
for THIS renormalized route, not the need for relative response control.
Normalizer moduli depend on the original norm and nome-dependent starRatio;
the response also depends on lag. No uniform changing-family modulus,
cross-width/nome carrier map, continuum survival or YM local-field
identification is supplied. The already-proved collapse of r^side remains
unchanged; norm one cannot improve that certificate.

## Declaration evidence

All paths are relative to the repository root.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `multiplicationDefect` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMultiplicationDefect.lean:37` | Actual polynomial C |
| `multiplicationDefect_supported` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMultiplicationDefect.lean:42` | Supported carrier retained |
| `sourceEnergy_shifted_multiplicationDefect` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMultiplicationDefect.lean:76` | Exact E=sS+s*mu*J-G |
| `sourceEnergy_centered_multiplicationDefect` | `lean/YMGap/Continuum/SU2QuaternionProductHeatMultiplicationDefect.lean:145` | Exact centered identity |
| `squareHeatMultiplicationDefect` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:60` | ORIGINAL active/source C |
| `squareHeatMultiplicationDefect_supported` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:67` | Actual square carrier support |
| `squareSignedHeatDefect` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:78` | Actual OWN-centered G |
| `paddedSquare_centered_source_firstMoment_zero` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:115` | SAME-source J=0 |
| `paddedSquare_energy_signedHeatDefect_identity` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:129` | Original E=sZV_own-G |
| `paddedSquare_normalizedEnergy_signedHeatDefect_identity` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean:160` | Original E/Z=sV_own-G/Z |
| `dyadicOriginalNorm`, `dyadicOriginalNormCauchy` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:57`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:59` | Actual norm and modulus |
| `dyadicOriginalNorm_pin`, `dyadicOriginalNorm_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:62`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:68` | OWN norm and positive original floor |
| `dyadicNormalizer`, `dyadicNormalizerCauchy`, `dyadicNormalizer_normalizes` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:73`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:79`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:85` | Computed inverse root and exact normalization |
| `dyadicUnitExcitation` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:96` | Actual SAME vacuum-complement unit state |
| `dyadicUnitExcitation_norm`, `dyadicUnitExcitation_norm_ne_zero`, `dyadicUnitExcitation_ne_zero` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:106`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:111`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:122` | Norm one and nonzero proofs |
| `dyadicUnitResponse`, `dyadicUnitResponseCauchy`, `dyadicUnitResponse_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:128`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:131`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:136` | Computed SAME-time response and modulus |
| `dyadicUnitResponse_geometric_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean:147` | Original relative fraction unchanged |

The reused inverse-root identity is `scalar_normalizes` at
`lean/YMGap/Continuum/PositiveCRealNormalizationScalar.lean:89`;
`vacuumComplementRealSmul` at
`lean/YMGap/Continuum/BF4WilsonAllNomeRealScalarLaws.lean:76` preserves the
actual vacuum complement.

## Precise remaining join: OPEN analytic producer

For m=side and a common 0<=eta<1, a sufficient finite signed-gain target is

    m*G >= (m*s-eta)*Z*V_own-zeta*Z

at computable late cutoff/depth thresholds for EVERY zeta>0, at each scale.
Algebraically this yields m*(E/Z)<=eta*V_own+zeta. This is the reviewed
BACKWARD TARGET, not a new checked scaling theorem or an inhabited analytic
bundle. No such useful bound on the actual G is provided by this milestone.
Favorable G may be large; neither s->0 nor absolute-smallness of G is
required. The stronger linear lag budget is only sufficient; a controlled
geometric propagation route remains possible.

The ENTIRE original energy and variance already have SAME completed-state
pins: `energyLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTemporalEnergyLimit.lean:218` and
`varianceLimit_completed_pin` at
`lean/YMGap/Continuum/BF4WilsonAllNomeMarginalVarianceLimit.lean:236`.
Separate limits of C or G and another completion wrapper are unnecessary.
The existing `lagMoment_endpoint_bound` at
`lean/YMGap/Continuum/BF4WilsonAllNomeMomentConvexity.lean:129` is the linear
lag consumer. If the missing bound were proved and passed through those
limits, it would give a relative lag-m floor 1-eta; norm-one rescaling would
then give an absolute scalar floor on the rescaled states.

That conditional scalar conclusion still does not construct common-carrier
cross-scale convergence, justify the observable renormalization as the
desired YM field, calibrate physical time/mass, prove full SAME QFT, or
realize every compact simple group. All those endpoints remain OPEN.
Finite additive errors are amplified by the inverse norm; the positive
starRatio can rescale tolerances at each fixed nome, but supplies no uniform
cross-scale modulus automatically. No source positivity shortcut or
angular-generator identity is inferred.

## Verification boundary

Three final focused target checks passed with one monitored worker, explicit
20-GiB ceiling and fresh process/memory/swap inspections. Their 4+6+15 printed
axiom outputs are ALL exactly {propext, Quot.sound}, without errors/warnings.
Independent Sol mathematical review and Luna evidence review cover the
results. No new sorry, axiom, choice, compiler-trusted decision, analytic
premise or weakened frontier is introduced. Root imports both concrete
consumers. Root/tree, broad audit/guard and progress metrics were NOT run.
CI and canonical chart remain unchanged; no paper-list/chart reprint.

The first concrete energy log (whnf timeout) and first unit log (notation
field parser error) are REJECTED. Opaque carrier definitions and scalar proof
typing repaired the former; parentheses around a local notation repaired
the latter. Neither changed a statement, guard or resource limit.

Accepted SHA256 evidence:

| Artifact | SHA256 |
| --- | --- |
| `lean/YMGap/Continuum/SU2QuaternionProductHeatMultiplicationDefect.lean` | `8ddba24dc0ff4085f1b79119c3e4d4c3375953baca24967202bf46e4352171b9` |
| `/tmp/ym-heat-multiplication-defect-20261002-first.log` | `80630f8bb5cf2e9d742e9cdbbf10c8b372611ea1d521eb6d405dd09a27850b74` |
| `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedHeatDefect.lean` | `35188c54678ff4492e0162ede73440baea5729b1c8e47b43accf844b5983da55` |
| `/tmp/ym-dyadic-square-signed-heat-defect-20261002-second.log` | `987e3ae1d8a505bb7dce6162d9975dd5b2576eaad20b27a3952c64a097dd3b34` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicUnitExcitation.lean` | `839dfe8d7e70f67f478770139a1aabde0635c6c2741a8ac27c4f85a36d37d051` |
| `/tmp/ym-dyadic-unit-excitation-20261002-second.log` | `f3615b216d6d303ef6077a66be38d52827db8e1ff2c6b79ff824baa146ebae92` |
