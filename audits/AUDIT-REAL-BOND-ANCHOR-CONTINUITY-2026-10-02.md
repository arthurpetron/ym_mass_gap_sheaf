# Uniform real time continuity of the original bond anchors

The previous integer-grid estimate now extends to every represented positive
real time increment on the SAME anchored physical bond states. A computed
radius is uniform in nome, width and scale at assigned geometric time.
This supplies equicontinuity, not a convergent or nonzero continuum theory.
The unchanged Clay Yang--Mills target remains OPEN.

## The actual dyadic and real time bounds

Write m=side(scale), u for the existing original unit Wilson-square excitation
and x_l for its existing physical bond point with value T(m+l)u. For every
dyadic mesh p, including zero steps, and every k, existing original dissipation
gives

    value(p) <= m*2^(-k)
      => squaredDistance(meshAction(p)(T(m+l)u),T(m+l)u) <= 2^(-k).

The unused time is nonnegative subtraction, not inverse transfer. The original
unit norm is exactly one. Positive meshes recover the existing bond action.
This is a linear small-time estimate; it does not infer a quadratic fractional
rate from the previous quadratic INTEGER increment bound.

For epsilon>0, define the computed geometric radius

    delta(epsilon) = 2^(-epsilon.den-1).

It is positive. The original lattice-time radius is m*delta(epsilon).
If the represented real time t is at most that radius, its original dyadic
approximants are eventually at most twice that radius. The exact doubled
budget is m*2^(-epsilon.den), and 2^(-epsilon.den)<=epsilon. The existing
increment rows, stored range witness and pairing-limit estimate pass the
dyadic ceiling to the SAME original real-time action.

Since m*spacing(scale)=1, the final physical-bond theorem reads

    spacing(scale)*realValue(t) <= delta(epsilon)
      => squaredDistance(action(t)x_l,x_l) <= epsilon.

Contraction and the existing addition law give the same radius for forward
increments at every positive real orbit time s. The radius is independent
of every strict nome 0<w<1, width with side<width, scale and l>=0. The
represented-row convergence moduli remain their own data; no uniform
cross-scale modulus is extracted from the real-order hypothesis.
Spacing here is assigned GEOMETRIC data, not a proved physical YM calibration.

| Declaration | Source | Checked content |
| --- | --- | --- |
| `anchoredMesh_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:72` | Every supplied mesh, including zero |
| `anchoredBond_dyadic_increment_bound` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:91` | Existing positive dyadic bond action |
| `anchoredRadius`, `anchoredRadius_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:102`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:104` | Computed positive geometric radius |
| `radius_double`, `half_den_small` | `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:115`, `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean:133` | Exact approximation slack and tolerance |
| `latticeRadius`, `latticeRadius_positive` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:62`, `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:69` | Original time radius as explicit data |
| `anchored_real_increment` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:75` | Original represented increment limit |
| `anchoredBond_real_increment` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:115` | SAME physical bond-value transport |
| `rescaled_time_bound`, `anchoredBond_geometric_real_increment` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:132`, `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:144` | Assigned-time uniform estimate |
| `anchoredBond_geometric_real_forward_increment` | `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean:153` | Every forward original real-time orbit |

The downstream action is the existing `BF4WilsonAllNomeBondOSRealTime.action`,
`lean/YMGap/Continuum/BF4WilsonAllNomeBondOSRealTime.lean:63`, with original-value
pin `action_value` at line 71. The proof uses the already constructed
`incrementRows_pin` and `incrementRows_limit` at
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeRealContinuity.lean:74` and
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeRangeRealContinuity.lean:82`.
No new time action, carrier, half-step shift, selected preimage or anchor
renormalization is used.

## The remaining forward backward join

The actual anchor has squared norm R(2m). Its exact response criterion still
retains curvature: R(2m)>=gamma iff 2m*e-C_(2m)<=1-gamma, by
`dyadicUnit_response_lower_iff`,
`lean/YMGap/Continuum/BF4WilsonAllNomeResponseCurvatureGain.lean:210`.
A useful positive gamma common to a justified changing family is still OPEN.
The source recurrence and existing signed overlap estimate do not produce
that bound; equicontinuity does not exclude a vanishing anchor norm.

Effective cross-scale anchored-Gram convergence with explicit moduli is still
OPEN. No common continuum carrier, canonical reflected half-space support
or essential surjectivity, local YM field identification, physical mass
calibration, full SAME QFT or every-group construction is supplied.
No displayed canonical chart claim is closed by this supporting result.

## Verification boundary

Both final focused targets passed using one monitored worker, explicit
20-GiB ceiling and fresh process/memory/swap checks before every launch.
The six dyadic and seven real-time gates use only propext and Quot.sound;
both radius definitions are axiom-free. Accepted logs have no errors or
warnings. Independent Sol mathematics and Luna evidence review passed.
No sorry, axiom, classical shortcut or new analytic premise is introduced.
Root imports both modules; root/tree, broad audit/guard and progress metric
were NOT run. CI and the exact canonical chart remain unchanged.

The first two dyadic logs are REJECTED: a half-power identifier resolved
to another in-scope half definition during rewriting, and a redundant bond
pin rewrite had no remaining occurrence. Explicitly scoping HalfPow.half,
typed scalar arithmetic and removing the duplicate rewrite repaired them
without weakening guards or bounds. The first real-time check passed but
had one unused-simp warning; removing that argument gives the accepted log.

| Accepted artifact | SHA256 |
| --- | --- |
| `lean/YMGap/Continuum/BF4WilsonAllNomeDyadicBondAnchorContinuity.lean` | `152edfda1ae6ea2e9b34ceeb0e237fbc9650fb81239528150118ecd655baafba` |
| `/tmp/ym-dyadic-bond-anchor-continuity-20261002-third.log` | `07de3b365b93ec234e3b57055a7f411d2b8ca0fd3aae9b594b99d7096a0ae546` |
| `lean/YMGap/Continuum/BF4WilsonAllNomeRealBondAnchorContinuity.lean` | `ebdb16f6caae7ae625ca173f6b99cf186f66351a867600e5e8d999cf81efeb5d` |
| `/tmp/ym-real-bond-anchor-continuity-20261002-second.log` | `587ca52365054c30df1330bd80f68758f8e9844612deb36fe516205e7ebb0f96` |
