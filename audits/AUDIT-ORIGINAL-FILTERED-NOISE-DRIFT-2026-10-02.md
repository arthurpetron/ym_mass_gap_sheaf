# Original filtered source: exact noise-minus-drift cancellation

The literal signed radius-two loop source now has an exact original
three-slice fold, including its original finiteValue normalization. It
retains a negative drift square before any estimate. This is not a
quantitative variance-relative bound or a continuum-survival theorem.

## Same original transfer, source and partition

Write g=terminalMessage n, T for the existing original transferStep and
ell for the existing weightedMass, including the full spatial weight. Set

    A = T(g),   B = T(g*f),   C = T(g*f^2),
    N = ell(A*C-B^2),
    D = ell((B-A*f)^2).

`driftPolynomial`, `driftSquare` and `noise`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredNoiseDrift.lean:71`,
`:77` and `:82`, use exactly these original objects. No terminal eigenmessage,
new conditional measure or replacement observable is assumed.

`numerator` at line 112 is the original observedMessage pairing in the
symmetric external window `(n,2,n)`. `filtered_loop_numerator` at line 217
proves, for the existing zero-time SourceLoop and every spin,

    numerator(sourcePolynomial(filteredExpression(loop 0 value spin)))
      = N-D.

The actual row `(f-lift_2 f)^2-(f-lift_1 f)^2` is expanded at coefficient
level. Original window contraction and weighted transfer symmetry give
AC, A^2*f^2, B^2 and A*B*f. Their combination is

    AC-A^2*f^2-2*B^2+2*A*B*f
      = (AC-B^2)-(B-A*f)^2.

This is the original signed source, NOT a claim that the one-step quartic
kernel represents the filtered TD slope.

`evenPartition` at line 91 is exactly
ell(terminal_(n+2)*terminal_n). `evenPartition_positive` at line 95 constructs
its positive original guard. `evenPartition_middle_pin` at line 100 proves
its original middle representation ell(A^2), by transfer symmetry and the
actual terminal recursion. This is an EVEN partition, not the finite odd
pair `(n+1,n)` and not its OWN variance.

`filtered_loop_windowRatio` at line 378 pins the existing windowRatio to
(N-D)/evenPartition. `filtered_loop_originalWindowScalar` at line 390
composes the existing original finiteValue pin, at cutoff headCutoff+stage
and the same `(n,2,n)` boundaries. Only that same positive partition is
inverted; no inverse variance or conditional density is introduced.

## Retained drift and honest open join

`driftSquare_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredNoiseDrift.lean:333`,
proves D>=0 from the original spatial certificate and the actual supported
drift polynomial. `driftPolynomial_shifted` at line 350 proves exact
coefficient-level invariance under f -> f-c, for any rational c. An OWN
center need not be replaced by a raw/channel center.

No noise positivity, finite N>=D, finite stationarity, finite odd/even
variance equality, useful scaling-family estimate or new joint limit is
asserted. The literal signed source already has its original joint-limit
and completed-response pins in `filteredIncrement_pin` and
`dyadicUnit_filtered_source_pin`,
`lean/YMGap/Continuum/BF4WilsonAllNomeFilteredIncrement.lean:61` and `:102`.
The forward task is to estimate the COMPLETE N-D, preserving D and all
source terms. The backward target remains a SAME-response lag-one reserve
and filtered budget relative to OWN interacting variance on a justified
family. Transport must use the existing original regulator moduli; it must
not silently replace the even finite partition by the odd one.

The full-product quartic Schur result is a separate raw-cost estimate, not
this missing relative bound:
`source_quarticProduct_signed_budget`,
`lean/YMGap/Continuum/SU2QuaternionProductHeatQuarticSchur.lean:375`.

## Verification

The final FOURTH focused monitored check exited zero. All twelve public
gates use only `{propext,Quot.sound}`; no final warning/error occurs.
Independent mathematical review passed. Earlier checks rejected namespace,
syntax and coefficient-representation mismatches, then an unspecified probe
and zero-offset simplification. The third check passed with one unused simp
argument, removed without disabling the linter. Mathematical statements,
guards and resource limits were unchanged throughout.

| Artifact | SHA256 |
| --- | --- |
| `BF4ExactSlabFixedSpatialFilteredNoiseDrift.lean` | `47feda0fb5d930bc689b43622c8cf1787504ebc6ff3f22df68bc15618bccb7d5` |
| `/tmp/ym-filtered-noise-drift-20261002-fourth.log` | `41f7b67eb4434351cb20ea94dd919376377c0a1442df524989fdd81118f90ab0` |

One worker, explicit 20-GiB ceiling and 12-GiB OS reserve. Fresh final preflight
showed 85 percent pressure-free memory and zero swap. Root import registered,
NOT aggregate-checked. No new sorry, axiom, classical shortcut, weakened
field, surrogate source, broad audit or CI change. No exact displayed chart
claim changes. Useful relative control, spatial/spacing control, continuum
survival, physical mass calibration, full SAME QFT, every compact simple
group and the Clay target remain OPEN.
