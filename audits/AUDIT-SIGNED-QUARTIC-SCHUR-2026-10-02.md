# Signed quartic Schur bound with raw source cost

The original one-link quartic kernel now has a constructive signed-source
upper bound with coefficient `60*(1-q)^2`. This valid identity-form bound
replaces the refuted universal squared-nome transport shortcut. Its cost is
the RAW Haar source square, not OWN interacting variance. The comparison to
that variance and the original filtered response remains OPEN.

## Original kernel and computed marginals

`quarticKernel`,
`lean/YMGap/Continuum/SU2QuaternionHeatQuarticSchur.lean:62`, is the literal
squared trace deficit times the original inclusive relative heat prefix.
`quarticKernel_supported` at line 81 proves two-link support.
`quarticKernel_certificate` at line 87 constructs a Type-valued ORIGINAL
square certificate from the existing heat certificate, for `0<q<1` and
`headCutoff q<=K`. No operator-positive-definiteness hypothesis is introduced.

`quarticKernel_upper_marginal` at line 170 and
`quarticKernel_lower_marginal` at line 230 prove BOTH actual endpoint
Haar marginals equal the original exceptional coefficient

    d(q) = 5 - 8*q^3 + 3*q^8,

times the retained one-link Haar insertion. The guard `2<=K` retains all
three vacuum coefficients. The lower marginal uses a proved complete
carrier exchange; padding recodings stay in the padded coefficient carrier.

## Signed bound and its actual cost

`quartic_signed_schur` at
`lean/YMGap/Continuum/SU2QuaternionHeatQuarticSchur.lean:276` proves, for
EVERY supported one-link rational polynomial a, with no sign restriction,

    H2[P(q,K)*a(lower)*a(upper)] <= d(q)*H1[a^2].

The proof applies the constructed kernel certificate to the actual square
`(a(lower)-a(upper))^2`. The two computed marginals give twice the difference
between the right and left sides. Only positive rational factor cancellation
is needed: no division, kernel PSD or positive-source assumption is used.

`quartic_signed_budget` at line 307 combines this with the existing exact
scalar ceiling `zeroCoeff_le_sixty`,
`lean/YMGap/Continuum/SU2HeatQuarticLowCoefficients.lean:216`, obtaining

    H2[P(q,K)*a(lower)*a(upper)] <= 60*(1-q)^2*H1[a^2].

The coefficient is independent of the degree of a and every later guarded
K; its nome dependence is explicit. This is a one-link Haar result, not a
full-width interacting or completed-transfer estimate.

`source_quartic_signed_budget` at line 317 substitutes `a=source*f` and
retains the exact cost `rawSourceMoment 1 source (f*f)`. The ORIGINAL
definition is `rawSourceMoment`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:119`:

    raw cost = H1[source^2*f^2].

This is NOT the interacting heat source moment or Z*OWNVar.
`rawMoment_difference_pin`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatMomentDefect.lean:123`, records
their signed heat-loss difference. No favorable sign or useful relative bound
on that difference is supplied by this milestone. The current local result
also does not tensorize the full retained product or project the inactive
fringe; those joins must retain the actual source before any global consumer.

## Next forward and backward work

FORWARD: extend the signed Schur calculation only through proved original
product marginals and the correct inactive projection, if needed by the
actual source. Retain its resulting raw source cost and signed correction.
BACKWARD: prove the original same-partition reserve and filtered slope
estimates recorded in
`audits/AUDIT-ORIGINAL-HAAR-FIXED-SOURCE-OBSTRUCTION-2026-10-02.md`.
No wrapper assuming either estimate is needed. Raw/OWN-variance alignment,
useful justified-family costs and the two-layer signed response input remain
OPEN; this local quartic result does not close them.

## Verification evidence and project boundary

The final focused monitored check exited zero with all eight public gates
within `{propext,Quot.sound}`; the kernel data uses no axioms. No final error
or warning occurs. Independent mathematical review passed. Earlier checks
rejected missing namespace opens and an unused binder; repairs were local,
without linter suppression, altered mathematical hypotheses or raised limits.

| Artifact | SHA256 |
| --- | --- |
| `SU2QuaternionHeatQuarticSchur.lean` | `024fcbd6111d549cfe57bddf86d47d5d596e5ca79b9a5acd56cedc0238298f39` |
| `/tmp/ym-quartic-signed-schur-20261002-third.log` | `4b91c26843e299a8471a3dddb1641b8bd12a2b5c6017575b1997961eb2c445ce` |

One worker, explicit 20-GiB ceiling and 12-GiB OS reserve; fresh preflight
showed 85 percent pressure-free memory and zero swap. One root import is
registered, NOT aggregate-checked. No broad build/audit, new sorry, axiom,
classical shortcut, weakened field, surrogate source or CI change.
No exact displayed chart claim changes; the chart is not reprinted.

Spatial/spacing control, nontrivial continuum survival, physical mass
calibration, full SAME-theory QFT, every compact simple group and the Clay
target remain OPEN.
