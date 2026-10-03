# Finite heat source gradients and conditional covariance

The finite heat defect now has a constructed angular inverse and an exact
pairing with derivatives of the entire original source. Independently, a
two-copy witness gives the sharp conditional coordinate covariance bound
with all spectator variables shared. The original BF4 quadratic gain has
a literal full-source consumer, retaining its finite moving-mean correction.
These results do not establish the changing-family relative budget or reserve.
The continuum theory, full QFT axioms, physical mass calibration, nontrivial
survival and every compact simple group remain open.

## Computed inverse and finite heat identity

`potential`, `lean/YMGap/Continuum/SU2QuaternionHeadCasimirInverse.lean:205`,
computes the finite Fischer modes and divides each positive-degree mode by
the rational reciprocal of d(d+2). The degree-zero head sector retains all
spectator polynomials. `zeroPart_projection` at line 213 identifies that
sector with the CONDITIONAL Haar projection, not the global mean.
`potential_poisson` at line 233 proves, under every original insertion,

    -L_head potential(p) = p - lift(partialHaarHead p).

The sign follows the original harmonic eigenvalue -d(d+2).
`source_gradient_identity` at line 301 then gives the exact Stein identity
by constructive angular integration by parts. The source is arbitrary and
is differentiated literally; no supplied inverse or Poisson equation is input.

`coordinateDefect_conditional_zero`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatStein.lean:120`,
proves conditional centering of the literal cutoff heat polynomial times
x_i-w^3*y_i, for K>=1. `coordinateDefect_source_gradient` at line 133
uses the computed potential to represent the actual finite heat pairing.
`coordinateDefect_retained_source_gradient` at line 161 leaves a surrounding
factor undifferentiated only with its explicit selected-head degree-zero proof.
No infinitesimal Ward identity is substituted for the finite heat defect.

`selected_coordinate_retained_source_gradient`,
`lean/YMGap/Continuum/SU2QuaternionSelectedHeatStein.lean:82`,
transports this identity to any distinct selected lower/upper pair on the
complete carrier, with supported entire source and retained polynomial.
The chart permutation is explicit; no spectator integration or independence
of the source is inferred.

## Sharp conditional covariance with shared spectators

`covarianceReplica_identity`,
`lean/YMGap/Continuum/SU2QuaternionConditionalCovarianceCertificate.lean:140`,
proves the exact two-copy wedge expansion. Only the integrated head is
copied; the output and every other variable remain shared. The actual weight
occurs in both copies. `conditionalGram_certificate` at line 201 integrates
the certified weights times the literal wedge square and scales by one half.
This constructs a Type-valued original certificate; no pointwise
positivity-to-certificate rule or covariance inequality is assumed.

Let P be the original conditional relative heat map retaining every tail
variable, L=P(q^2)-(Pq)^2 and C_i=P(q*x_i)-(Pq)*w^3*y_i.
`coordinateCovariance_certificate`,
`lean/YMGap/Continuum/SU2QuaternionRelativeHeatCoordinateCovariance.lean:293`,
constructs a certificate for

    ((1-w^8)/4)*L - C_i^2.

Its explicit hypotheses are 0<w<1, K>=max(headCutoff(w),2), source support
and a nonempty retained output. The entire signed source may depend on the
output link and every spectator. Actual conditional normalization, coordinate
mean and second moment are proved by `conditional_normalization` at line 104,
`coordinate_mean` at line 113 and `coordinate_secondMoment` at line 125.
The variance is (1-w^8)/4+(w^8-w^6)*y_i^2. Its positive cap correction is
(w^6-w^8)*y_i^2, not an absolute source derivative bound.
`spectator_covariance_bound` at line 342 permits any certified retained action.

Only `sourceLoss_raw_pin` at line 360 adds output-link degree-zero support
to identify the integrated loss with raw Haar q^2 minus the conditional
output square. Neither this raw loss nor L is identified with the original
interacting OWN variance or a completed OS norm. The rate depends explicitly
on w; the cutoff also depends on w. No beta-uniform or scaling estimate follows.

## Original BF4 gain consumer

`fullSourceDefectPair_transfer`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredGainSourcePair.lean:89`,
folds the original doubled-carrier defect under the entire lower source
q=V*g_n and upper test r=V*b. Here A=Tg_n, b=T(g_n*(f-c)), and the
literal defect is f(x)-a*f(y). Both original spatial weights occur once.
`commutatorGain_source_pair` at line 155 proves for arbitrary rational c,a

    G2 = fullSourceDefectPair + (a-1)*c*ell(A*b).

The finite OWN mean may be substituted, but it does not make ell(A*b) zero:
that mean belongs to the odd marginal, while this pairing has the actual
mixed/even weight. No stationarity or centered free eigenpin is used.

## Forward and backward proof faces

The forward face supplies literal finite heat source-gradient identities
and constructed conditional covariance certificates. The backward face is
the existing SAME completed-state survival consumer
`dyadicUnitResponse_filtered_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicFilteredGeometricSurvival.lean:154`:
R1>=gamma0>0 and m*(R1-R2)<=C*R1, with Nat C>=1,m>=4C.
The accepted finite-gain limit joins these faces to C2-a*C1 on that same
carrier; see the preceding quadratic-gain audit.

The missing quantitative join is a useful SIGNED full-source gain bound
relative to the SAME interacting lag-one reserve on a justified changing
family. A conditional source-loss cost or a raw source-gradient norm cannot
silently replace that reserve. The exact moving-mean residue must also be
paid with the original boundary moduli. Family-wide C and gamma0 remain open.

## Focused verification evidence

Each accepted source below was checked separately with one Lean worker,
12 GiB OS reserve and explicit 20 GiB worker ceiling after a fresh live
memory/process/swap preflight. All printed dependencies are contained in
{propext, Quot.sound}; no new sorry, axiom or classical shortcut was introduced.
An initial degree-zero proof had a classical dependency; its replacement
uses explicit Nat zero-sum elimination and the final check below passes.
Independent mathematical reviews and source/log QA passed. Root imports
are registered, not aggregate-checked. No broad build, audit, CI or chart
change is claimed.

| Source basename | Accepted log under /tmp | Printed gates |
| --- | --- | --- |
| SU2QuaternionHeadCasimirInverse.lean | ym-head-casimir-inverse-20261002-final.log | 9 |
| SU2QuaternionRelativeHeatStein.lean | ym-relative-heat-stein-20261002-third.log | 4 |
| SU2QuaternionSelectedHeatStein.lean | ym-selected-heat-stein-20261002-third.log | 3 |
| SU2QuaternionConditionalCovarianceCertificate.lean | ym-conditional-covariance-20261002-first.log | 7 |
| SU2QuaternionRelativeHeatCoordinateCovariance.lean | ym-relative-heat-coordinate-covariance-20261002-fourth.log | 11 |
| BF4ExactSlabFixedSpatialFilteredGainSourcePair.lean | ym-filtered-gain-source-pair-20261002-third.log | 4 |

Sources are under `lean/YMGap/Continuum/`. SHA256 pairs (source, accepted log):

- HeadCasimirInverse: `66ac9ce71cbeb223bb8acb573444bc0ad677b054fc22d94b3d8ee7b7af7c6644`, `53a2ba40d09c4184fb83870f0e7e3ff93626266a48f7184a495ca17eeb3a6462`.
- RelativeHeatStein: `2672bde59a6699f529b140a8aadb6fa3a961b47f21d9be077d443a52b7d20fea`, `74ec63dcfb63e8e6fe2c3fc3c8355a7001fe05e40c59a6752d15bcbd1886a412`.
- SelectedHeatStein: `be20f77ac61dc567c2b18357c45b496237f3e574cbbcdad8670f336ef7ad04ca`, `4baab4114ccad5e5349307c0154fc074e744bc84997e7b5119f94534dfac1734`.
- ConditionalCovarianceCertificate: `e2eb2cbac31aed7170269ea8e482bcc2133db7975fcec422a866c1d20001a00a`, `ec82cebb3a70f211e5895c743fc2b4c6dc468240bc0bbdc31e24827d9d08f5a3`.
- RelativeHeatCoordinateCovariance: `a1bb1de35580a7382f0326b6f829f73cf9776b5aa8274729eafec6a56529b716`, `10c79cdee5c51d047308cbbb2650f492fd38d92919188084265f741b9f200d0d`.
- FilteredGainSourcePair: `65227c9a64d74cbf361512c1e7f02536245cb0d89e6e43f809760fc76de67e98`, `f7aa87822f827508f867cf6a98453241bb2a522707977c92818b7a6171f5a8f1`.
