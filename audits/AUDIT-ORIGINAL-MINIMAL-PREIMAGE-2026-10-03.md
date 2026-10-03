# Least norm of the original half-anchor preimage

The whole-project goal remains OPEN: nontrivial continuum Yang--Mills on
R^4 for every compact simple group, SAME-theory QFT axioms and a finite
positive physical mass gap. This checkpoint is an original-carrier
least-norm theorem, not a uniform cap or a scaling-survival theorem.

## Checked mathematical increment

Fix the original completion, its actual transfer T and inner product B.
Let s=side(scale)>=2, h=s/2, u be the existing dyadic unit excitation,
alpha the existing anchor normalizer, z the existing normalized anchor,
and y0=alpha*T(h)u the existing constructed preimage. Its exact pin
T(h)y0=z is unchanged. For ANY y in the SAME completion with T(h)y=z,
put d=y-y0. Then

    T(h)d=0,
    B(y0,d)=alpha*B(u,T(h)d)=0,
    B(y,y)=B(y0,y0)+B(d,d),
    B(y0,y0)<=B(y,y).

The first equality uses actual transfer linearity; the second uses actual
time balance. The final inequality uses the original completed norm's
nonnegativity. No transfer inverse, injectivity, ambient-kernel deletion,
macro ratio or independent positive norm floor is assumed.

All new claims retain 0<w<1, side(scale)<width, side(scale)>=2 and the
literal equality T(side(scale)/2)y=z. They quantify over the original
completed y, not an auxiliary polynomial or a surrogate carrier.

## Exact declarations

| Declaration | Source | Role |
|---|---|---|
| `halfAnchorPreimage_difference_orthogonal` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicMinimalPreimage.lean:85` | Difference is orthogonal to the constructed original preimage. |
| `halfAnchorPreimage_norm_decomposition` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicMinimalPreimage.lean:99` | Exact Pythagorean squared-norm identity. |
| `halfAnchorPreimage_norm_minimal` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicMinimalPreimage.lean:115` | Constructed preimage has least squared norm among all exact preimages. |
| `halfAnchorPreimage` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:167` | Existing literal alpha*T(side/2)u construction. |
| `halfAnchorPreimage_pin` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:171` | Existing exact original half-time pin. |
| `halfAnchorPreimage_norm_cleared` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:115` | Existing cap consumer of the SAME macroscopic response ratio. |
| `normalizedAnchorResponse_block_floor` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132` | Existing all-integer-block survival consumer of that ratio. |
| `response_anchor_bridge` (private) | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedAnchorContinuity.lean:175` | Existing sufficient relative one-step budget-to-ratio implication. |

## Forward/backward routing consequence

Changing the exact preimage cannot reduce its squared norm. The new theorem
therefore rules out treating a cheaper choice of exact preimage as an
independent route around the existing preimage's quantitative cost. It
does not establish that cost uniformly on a changing family.

The backward survival consumer needs kappa*R(s)<=R(2s), with a supplied
positive kappa on a justified family. A relative one-step signed-cost
budget is one sufficient way to produce that input, not an extra
requirement if the ratio can be proved directly. Those existing consumer
declarations were source-reviewed here, not recompiled. No new survival
wrapper, frontier structure, hypothesis field or normalization was added.

The next analytic input remains unpaid. Retain the original full action,
terminal sources, filtered response and chronological OWN center in its
signed estimate. Physical time/scaling calibration, canonical reflected
OS realization, continuum survival, full QFT and every-group construction
remain independently OPEN.

## Verification boundary

Accepted focused target:
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicMinimalPreimage.lean`.
Completed 2026-10-03 UTC; accepted log:
`/tmp/ym-original-minimal-preimage-20261003-a.log`.

The monitored launcher exited zero with one worker, a 20 GiB worker cap
and 12 GiB OS reserve. Dynamic preflight found no competing compiler or
runner, 84% memory-pressure free percentage and zero swap. Exactly three
printed gates each report only {propext, Quot.sound}; no error, warning
or sorryAx. Independent read-only evidence review confirmed source/log
hashes, original carrier, guards and axiom outputs.

Source SHA256:

    c05e01755b66fb33fd74c9e3e909b13fbbce40d3e0c8dbec293f349f060e5e6e

Accepted-log SHA256:

    3c89fb0b275b35099206c10706671e20dd3d842ae2245263002cab9365a4596a

Root import registration only; no aggregate build, full audit or broad
guard was run. No sorry, new axiom, classical shortcut, surrogate or
frontier weakening. The exact canonical ASCII block and CI are unchanged;
no displayed goal box is closed by this supporting theorem.
