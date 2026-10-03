# Three norm projective comparison on original Wilson anchors

Three relative quadratic estimates now suffice to control BOTH normalized
response errors on the ORIGINAL all-nome Wilson dyadic anchors. The proof
does not require a uniform positive raw norm floor. This is a checked
conditional consumer: producing the three estimates on a justified changing
family remains OPEN, as do physical calibration and the continuum Clay target.

## Homogeneous estimate

`twoSided`, `lean/YMGap/Continuum/RCThreeNormProjectiveComparison.lean:32`,
means that BOTH signed differences of two RC values are at most the budget.
The common scale lambda is a nonnegative RC, with no chosen representative
or inverse. Suppose 0<=delta<=1/2 and each of the three quadratic costs obeys
abs(Q_k-lambda*Q_l)<=delta*lambda*Q_l. The costs are the anchor norm N
and the plus/minus polarization diagonals Qplus, Qminus. With
4*C_i=Qplus_i-Qminus_i, Qplus_l+Qminus_l<=4*N_l and both signs of C_l<=N_l,
`three_norm_projective_compare`, same module:277, proves

    BOTH signed errors of C_k*N_l and C_l*N_k <= 4*delta*N_k*N_l.

Polarization first bounds C_k-lambda*C_l by delta*lambda*N_l in both
orders. The norm comparison gives lambda*N_l<=2*N_k. A constructive
interval-product inequality then clears the comparison. No N inverse,
positive raw norm floor or carrier map is used; zero norms and lambda=0
remain valid generic cases. `twoSided_mul_right`, same module:146, preserves
both bounds under a supplied nonnegative factor.

This sufficient three-cost criterion is not claimed to be logically weaker
than direct normalized-response convergence. It reduces the sufficient
producer to a finite homogeneous set of quadratic costs, not a full-form
or full-width domination theorem.

## Actual original carrier consumer

All declarations in this section are in
`lean/YMGap/Continuum/BF4WilsonAllNomeThreeNormComparison.lean`.
Each theory has its OWN nome 0<w<1, literal width, existing Completion,
completedInner B and completedTime T. The two theories are never identified
through a width map. The actual costs are:

- `normSq`:129: B(x,x).
- `plusSq`:133: B(x+T(j)x,x+T(j)x).
- `minusSq`:137: B(x-T(j)x,x-T(j)x).
- `response`:131: B(x,T(j)x).

`response_polarization`:157 proves the exact polarization identity.
`plus_minus_sum_bound`:163 and `response_signed_bound`:174 prove the
required inequalities from the actual form positivity and time contraction,
including zero anchors. `three_norm_response_compare`:286 instantiates the
homogeneous theorem on two separate original carriers and time indices.
Its ONLY cross-theory estimates are the three explicit supplied relative costs.

`dyadicAnchor`:202 is the EXISTING centered unit excitation advanced by its
own side length. `dyadicAnchor_vacuum`:205 retains vacuum orthogonality.
`dyadicAnchor_norm_pin`:210 and `dyadicAnchor_response_pin`:217 identify
the SAME anchor norm and response with the existing original dyadic response
representatives. Each theory retains its OWN mean and parameters.

`normalizerSquare`:226 is the square of the EXISTING computed anchor
inverse-root scalar, not a newly chosen inverse. Its nonnegativity, exact
normalization and response pin are checked at :230, :236 and :243.
`dyadic_normalized_response_compare`:313 multiplies the cleared estimate by
both such squares and uses the exact norm pins to prove

    BOTH signed errors of normalizedAnchorResponse_k(j_k)
                      and normalizedAnchorResponse_l(j_l) <= 4*delta.

The existing parameter-dependent norm floors are used only by their existing
normalizer construction; NO uniform raw floor or uniform inverse is assumed.
This result does not construct any of the three relative costs, an error
modulus across a family, physical matching of j_k and j_l, a continuum
functional, a complete OS algebra or a calibrated physical mass.

## Parallel forward review and next input

The separate source review still finds no favorable sign from the local
radial square estimate: `paddedSquare_own_commutatorGain_local_radial_bound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainRadialCost.lean:258`,
bounds the SQUARE of the gain minus the retained mean residue.
`gainLimit_completed_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredGainLimit.lean:133`,
identifies the gain as C2-a*C1. Thus the relative heat-loss deficit still
retains (1-a)*C1 minus that SIGNED gain; the square bound supplies no sign.
This is source review, not a newly proved relative-energy estimate.

The next substantive inputs are the actual three relative quadratic costs
and the actual family-wide macroscopic response ratio on a justified
changing family. Do not add more normalization/polarization wrappers to this
now-checked consumer branch or replace a reflected signed cost by an ordinary
variance/density comparison. Physical-time/local-field identification, full
QFT structure and every compact simple group remain OPEN.

## Verification boundary

Root checked only these two sources, serially through the monitored launcher,
jobs=1, reserve=12 GiB, worker cap=20 GiB. Fresh preflight before each launch
showed 85 percent system-wide free memory, zero swap and no competing build
or runner. The accepted SECOND checks both exited zero, with no warnings.
All twenty public gates are exactly {propext, Quot.sound}; there is no
`sorryAx`, classical input or native-decide dependency. First rejected checks
caught a quotient-function rewrite and an opaque square elaboration issue;
they are not proof evidence. Independent source/log review passed.

- Generic source SHA256: `7d859ceb34f67c146a38e5165c61fac2df3aa70e134ab3d5b4161cebe895338f`.
- Generic accepted log: `/tmp/ym-three-norm-projective-20261003-second.log`.
- Generic log SHA256: `f9674f448baf77ab8ea3aa0bf4aed162405c868e83c45773612bf6b1832a2fc7`.
- Wilson source SHA256: `61e77046c37f9662da43437bda0d7dfb34292481728b0384141ce046f697b2bb`.
- Wilson accepted log: `/tmp/ym-wilson-three-norm-20261003-second.log`.
- Wilson log SHA256: `c7b86b6da19cad0ddbbea114133acf5e897fed036aa67835368178bb7cffd69d`.

No full build or repository-wide audit was run. Root imports are registered,
NOT aggregate-checked. No sorry, axiom, classical shortcut, new frontier
bundle, canonical field weakening or CI change was introduced. No exact
canonical chart claim changed; no ASCII chart was reprinted.
