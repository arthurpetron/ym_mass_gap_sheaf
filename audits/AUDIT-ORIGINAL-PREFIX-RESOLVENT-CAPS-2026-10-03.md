# Computed log-prefix caps for the existing original inverses

Whole-project goal: nontrivial continuum Yang--Mills on R^4, every compact
simple group, SAME-theory QFT axioms and a finite positive physical mass gap.
That target remains OPEN. This is fixed-nome/width backward quantitative
control on the actual existing SU(2) carrier, not a physical uniform bound.

## Exact consequence

Let r be the original kinetic floor/cap fraction and
gamma_N=sum_(j=1..N) r^j/j. For every N>=1, gamma_N>0 is proved. On the
original vacuum complement, the existing positive resolvent R_lambda and
zero-shift inverse obey, respectively,

    B(R_lambda x,R_lambda x) <= (lambda+gamma_N)^(-2) B(x,x),
    B(H_inverse x,H_inverse x) <= gamma_N^(-2) B(x,x).

The original domain equation supplies B(u,x)=lambda*B(u,u)+B(u,H u).
The already proved domain prefix floor bounds the second term. Existing
square-completion coercivity converts this form estimate to the norm cap.
For the zero-shift inverse the existing domain output is exactly x. No
norm of an unknown vector is inverted and no new inverse is constructed.

## Source anchors

All paths below start with `lean/YMGap/Continuum/`.

| Declaration | File:line | Role |
|---|---|---|
| `prefixGap_nonnegative` | `BF4WilsonAllNomeDomainLogPrefixResolventGap.lean:52` | Computed prefix nonnegativity. |
| `prefixGap_positive` | `BF4WilsonAllNomeDomainLogPrefixResolventGap.lean:81` | Every nonempty prefix is positive. |
| `positive_resolvent_prefix_norm_bound` | `BF4WilsonAllNomeDomainLogPrefixResolventGap.lean:110` | SAME positive-shift inverse norm cap. |
| `zeroShift_prefix_norm_bound` | `BF4WilsonAllNomeDomainLogPrefixResolventGap.lean:123` | SAME existing zero-shift inverse norm cap. |
| `domain_log_prefix_gap` | `BF4WilsonAllNomeDomainLogPrefixGap.lean:97` | Existing actual domain form producer. |
| `norm_from_coercivity` | `BF4WilsonAllNomeSectorResolventGap.lean:91` | Reused square-completion argument. |

## Verification boundary

One serialized focused check exited zero using the monitored launcher,
one worker, 20 GiB ceiling and 12 GiB OS reserve. All four printed gates
depend only on {propext, Quot.sound}; no error, warning or sorryAx.
Accepted log: `/tmp/ym-original-prefix-resolvent-20261003-a.log`.

Source SHA256:
`3002c266c5f9e6ea96a4eeb42be7641dd8002be14ba1b1dc7b700b366fb63653`.
Accepted-log SHA256:
`6e7d12a07c6392fe2940fbc62638498c373f7da6541cc34454c2317033d78867`.

No scalar infinite log or CRealLog equality, physical normalization,
spacing/volume-uniform bound, new inverse, surrogate, sorry, axiom or
frontier weakening. Root imports registered only; no aggregate build,
full audit or broad guard. Exact canonical chart and CI are unchanged.
The complete signed relative estimate on a justified family, canonical OS,
nontrivial continuum survival, physical calibration, full QFT and every
group remain OPEN.

## Source-reviewed execution boundary

The existing `mixFraction_le_width_power`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRateWidthObstruction.lean:74`,
proves r(w,width)<=32^(-width) for every strict nome. That is a bound on
this computed coefficient, not the actual spectral gap. It is historical
checked source reused for planning, not a new check or new theorem here.
No newly checked infinite-prefix ceiling is claimed. Further scalar/cap
expansion is not the current physical/scaling producer. The existing
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`,
still explicitly consumes the unpaid SAME kappa*R(side)<=R(2*side) estimate.
