# ORIGINAL second-order vacuum mismatch — 2026-10-04 UTC

PROGRESS after `4b6ac0b`: an actual finite error coefficient is improved;
the aggregate survival producer and continuum/Clay target remain OPEN.

## Mathematical increment and actual consumer

Keep the ORIGINAL ell=H[V*(-)], T=P M_V, a=g_(s+1), A=T a and
z=ell(a^2), p=ell(a*A), v=ell(A^2), q=ell(A*T A), M=z*q-v*p.
The existing terminalComparison constructs l*a<=A<=U*a in the actual
polynomial certificate cone, with 0<l and U-l<=eta*l.

Two products of THESE certificates, not a pointwise or eigenvector premise,
give

    v <= (l+U)*p-l*U*z,
    q <= (l+U)*v-l*U*p.

The second product is (A-l*a)*T(U*a-A); actual weighted symmetry pins
ell(a*T A)=ell(A^2). With x=p-l*z>=0, y=U*z-p>=0 and
k=(l+U)*z-p=l*z+y>=0, the exact scalar identity is

    (l+U)*x*y-M
      = z*((l+U)*v-l*U*p-q)
        + k*((l+U)*p-l*U*z-v) >= 0.

Then 4*x*y<=(x+y)^2, x+y<=(eta*l)*z,
l+U<=(2+eta)*l and p*v>=l^3*z^2 yield

    4*M <= (2+eta)*eta^2*p*v.

`terminal_vacuum_mismatch_quadratic_upper`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostTransport.lean:454`,
constructs this bound at every K>=headCutoff(w), 0<w<1 and s>=0.
Its scalar algebra is `mismatch_second_order` in the same file:354.
No source norm is inverted. The only normalized intermediate, used to
prove U>=0, is the existing terminalMassRatio_bounds on the already-proved
positive ground-message norm. No new analytic hypothesis is added.

The DIRECT consumer `terminal_clearedRayleighCost_quadratic_vacuum_transport`,
same file:545, retains the entire residual R and both signed costs:

    4*(z^3*Do+v*R)
      <= 4*v*p^2*Di + z^2*(2+eta)*eta^2*p*v*B.

`original_block_clearedRayleighCost_quadratic_vacuum_transport`, same
file:591, pins it to a=g_(n+t), c=T^t(g_n*psi), A=g_(n+t+1),
b=T^(t+1)(g_n*psi), eta=comparisonEta(w,width,n+t-1), with 1<=n+t.

The already-proved payment p*Di^2<=C*R is retained simultaneously:

    4*(C*z^3*Do+p*v*Di^2)
      <= 4*v*p^2*C*Di + z^2*(2+eta)*eta^2*p*v*C*B.

This is `terminal_clearedRayleighCost_quadratic_vacuum_damping`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRayleighCostCoercivity.lean:237`,
and its ACTUAL block specialization
`original_block_clearedRayleighCost_quadratic_vacuum_damping`, same file:303.
The SAME fixed psi/initial OWN center, incoming C, outgoing B and all
distinct ground partitions remain. Zero/signed sources and t=0 with n>=1
are included; no Di>=0 or nonzero-excitation premise appears.

## Improvement and open boundary

The new coefficient is (2+eta)*eta^2/4, versus the retained older eta.
It is genuinely second order as eta tends to zero, and sharper for
0<eta<=1; it is NOT asserted sharper for every eta. The older linear
theorems remain unchanged and available. Eta depends on nome and width;
this is not a scaling-uniform estimate. Generic damping still permits
persistent relative attenuation.

The backward consumer remains `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Its useful aggregate bound versus SAME surviving variance on a JUSTIFIED
changing family is not supplied. Both signed Taylor terms remain inside
the complete Di and Do; no source/cost replacement is made.

Parallel source scouts confirmed that
`paddedSquare_oddVariance_floor`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareOddVarianceFloor.lean:121`, already
has a width/depth/cutoff-independent floor starRatio(w). It is not a
macroscopic-time retention estimate or a nome-to-one uniform floor.
`centered_source_square`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`,
uses q*Pq, whereas `centeredMixedMoment`, same file:130, uses q^2. OWN
centering does not identify those weights. The Wilson source-gradient
identity `paddedSquare_own_commutatorGain_source_gradient`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareFilteredGainStein.lean:190`,
retains differentiated V*g_n and its finite mean correction; no useful
source-specific cumulative signed flux bound was found by these scouts.

A targeted primary-source screen, not another listing scan, supplied no
such estimate: the [Villain action paper's introduction](https://arxiv.org/html/2404.09928v1)
restricts its Ginibre consequence to abelian symmetry, while
[Abdesselam's section 1](https://arxiv.org/html/2207.07603v2) explicitly treats
related non-abelian spin-model correlation inequalities as open and proves
different asymptotic/determinantal results. Neither is imported as a
four-dimensional gauge correlation premise.

## Verification

Two final serialized focused checks passed, with **17 reported gates**
(10 Transport, 7 Coercivity), all exactly `{propext, Quot.sound}`.
All five new public declarations have explicit gates. Independent Sol
mathematical/source review passed both the producer and its consumers.

- Transport source SHA-256: `8d15a5dd4f3cf9386410cc46d3656c9bdcc71d83f1ecdc1b16dc92cf06e587b8`.
- Coercivity source SHA-256: `5c867f1d14e777ba83eee07ccf12e5b5ca2565f972df45940e96645ac399541f`.
- Accepted Transport log: `/private/tmp/ym-rayleigh-vacuum-quadratic-20261004-2.log`, SHA-256 `38b89ce68c60915fa43e02e2baa97627375ce530412f04afa50e3704dd50acfa`.
- Accepted Coercivity log: `/private/tmp/ym-rayleigh-vacuum-damping-20261004-1.log`, SHA-256 `a1dfd72ae2c80ff75fb1825d44b60cbc5461d755a5283d123815ad20461b3958`.

The first rejected Transport check had two elaboration errors: missing
PolyExpr annotations and a scalar nonnegativity argument. Both were fixed
without raising resources. Each launch had a fresh process/swap/pressure
preflight: no competing compiler/runner, zero swap, 76–77% free. One worker,
20 GiB ceiling, 12 GiB reserve and monitored launcher were preserved.

No new module/root import, sorry, axiom, frontier field, CI change or resource
increase. No full/root build, axiom audit, guard or broad metrics ran.
Historical reports retain their original checked-source hashes and line
anchors; current declarations are cited above. Canonical chart atoms are
unchanged, so no ASCII reprint. Survival, physical calibration, canonical
OS/full QFT, continuum construction, every compact simple group and Clay
remain OPEN.
