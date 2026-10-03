# Original block-source Rayleigh split and paid finite-boundary drift

## Checked mathematical increment

Keep the original transfer T=P_w M_V and ell(p)=H[V*p]. For any supported
original source g and supported test psi, set A=T^t g, b=T^t(g*psi),
u=A*psi, r=b-u, Z0=ell(A^2), Z1=ell(A*T A). The two partitions are
DISTINCT. The cleared vacuum-subtracted cost is

    D = Z1*ell(b^2) - Z0*ell(b*T b).

The new exact identity is

    D = Z0*energy(A,psi)
        + ell(A*psi^2*(Z1*A-Z0*T A))
        + ell(r*(Z1*(b+u)-Z0*T(b+u))).

It is kernel-checked for the literal original block sources, including
t=0. No division by A or Z0, finite eigenvector pin, favorable sign or
extra analytic estimate is assumed. The last pairing is kept SIGNED and
combined; its summands are not replaced by separate absolute bounds.

The source defect r is exactly T^t(g*psi)-psi*T^t g. Subtracting ANY
rational constant from psi leaves r unchanged. Thus the SAME computed
finite OWN mean can be retained without a mean-zero or centered-eigenvector
assumption. This does not say that the whole signed cost is center-independent.

The second term now has an actual quantitative estimate. For
A=T^(s+1)1, every supported psi, 0<w<1, and K>=headCutoff(w),

    abs ell(A*psi^2*(Z1*A-Z0*T A))
        <= eta(w,width,s)*Z1*ell(A^2*psi^2),

where eta is the already computed comparisonEta. The new joined upper bound
therefore pays the finite-boundary term while retaining original energy
and the combined signed commutator cost. Eta is independent of guarded K,
NOT of w or spatial width. The existing explicit comparisonOnset pays any
positive tolerance at fixed w/width; no physical spacing dependence is erased.

## Declaration-to-source map

All paths below are repository-relative. Declaration names are local names
in the cited module's namespace under YMGap.Continuum. The fixed-spatial
module prefix is written out in paths.

| Declaration | Source | Exact role |
| --- | --- | --- |
| `originalBlockTransfer` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:40` | Literal iterateStep with original kinetic and spatial weights. |
| `blockMultiplicationDefect` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:44` | Complete original block multiplication commutator. |
| `blockMultiplicationDefect_zero` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:99` | Zero-step defect equals zero at coefficient equality. |
| `blockMultiplicationDefect_succ` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:107` | Transfers the old defect and adds one-step defect on the actual evolved source. |
| `blockMultiplicationDefect_shifted` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockMultiplicationDefect.lean:154` | Exact invariance under any rational constant shift. |
| `clearedRayleighCost` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:131` | D with original weighted pairing and distinct Z0/Z1. |
| `boundaryDrift` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:136` | Literal signed finite-boundary insertion. |
| `signedMultiplicationCost` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:144` | One signed original commutator pairing. |
| `clearedRayleighCost_split` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:204` | Exact split, supported b and A*psi only. |
| `original_block_rayleigh_split` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:234` | Instantiates the split on actual T^t g and T^t(g*psi). |
| `original_block_defect_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:250` | Identifies the split's r with the literal block commutator. |
| `boundaryDrift_terminal_abs_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:261` | Original boundary estimate joined to this exact split. |
| `terminal_clearedRayleighCost_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:273` | Actual upper bound paying boundary drift, leaving energy/signed cost explicit. |
| `clearedDrift` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalRayleighDrift.lean:45` | Literal original terminal insertion. |
| `clearedDrift_pin` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalRayleighDrift.lean:55` | Exact scalar expansion Z1*Epsi-Z0*Mpsi. |
| `clearedDrift_bounds` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalRayleighDrift.lean:135` | Both signed orders with computed eta. |
| `clearedDrift_abs_le` | `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalRayleighDrift.lean:216` | Absolute boundary cap, without a new estimate premise. |

Existing inputs are `transferStep_weighted_symmetric`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:97`,
`terminalComparison` and `terminalComparison_relative_width`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalComparison.lean:230`
and `:306`, and the actual positive pairing theorem `terminalPair_positive`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalBracket.lean:149`.
The explicit tolerance modulus is `comparisonOnset` and its theorem
`comparisonEta_small`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTerminalEnergyComparison.lean:371`
and `:377`. The OWN mean is the existing `mean`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonMeanRadial.lean:99`;
the new split does not replace it or construct a new center.

## Actual consumer and remaining input

The backward producer target remains the same: for the ACTUAL growing
padded square, side s>=2, t=s/2, original g_n and SAME finite odd mean c_n,
prove a useful changing-family bound

    s*D <= C*ell(b^2)*Z1,  b=T^t(g_n*(f-c_n)).

This estimate is UNSUPPLIED. The new result pays only finite-boundary drift;
it still uses ell(A^2*(f-c_n)^2), NOT ell(b^2). The comparison to the latter
and the combined signed energy/commutator estimate remain open. No favorable
sign for either separate contribution is asserted. No bare product-heat
gradient estimate or the finite six-link bent-cube pilot is substituted for
the actual growing planar Wilson square.

The original finite chronological source/partition join and joint-limit
passage remain separate work. Changing centered polynomials are not passed
through a fixed-expression limit. Even a useful finite relative estimate
must reach the SAME completed original response before it supplies
`normalizedAnchorResponse_block_floor`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicNormalizedMacroRatio.lean:132`.
The three cross-scale relative costs remain inputs of
`dyadic_normalized_response_compare`,
`lean/YMGap/Continuum/BF4WilsonAllNomeThreeNormComparison.lean:313`.
The justified physical family, physical calibration, full SAME-theory QFT,
every compact simple group and continuum Clay target remain OPEN.

## Verification boundary

Root ran the three smallest module checks serially through
scripts/safe_lean_build.py, jobs=1, reserve=12 GiB, hard worker cap=20 GiB.
Every launch had fresh process/memory/swap checks: 85--86 percent system-wide
free memory, zero swap and no competing Lean/Lake/pytest/runner. The three
accepted checks exited zero; direct parsing found 17 unique printed records,
all within {propext, Quot.sound}, without errors, warnings or sorryAx.
Rejected preliminary logs contain elaboration/parser/transport errors and
are NOT accepted proof evidence. Independent read-only source/algebra review
confirmed the signs, original action and absence of stationarity assumptions.

| Module | Source SHA256 | Accepted log | Log SHA256 |
| --- | --- | --- | --- |
| BlockMultiplicationDefect | `f1e7938b40ae9348b7e9d42a3765081526901165f61eeb3f7f4c3957eeb3966b` | `/tmp/ym-block-defect-20261003-b.log` | `c28efa54b122de1d8db2f376c55726d54b822642b1ba45b8afea46e02b58bb75` |
| TerminalRayleighDrift | `59cdcbdf92f3302f2d562ea725bfbd9d9f94666274179b9c169137a5e910010e` | `/tmp/ym-terminal-rayleigh-drift-20261003-d.log` | `c0caa0f2a56e909355fc60f205bdeece78328d35d8a8ddf7edd272f542b57f04` |
| BlockRayleighSplit | `6575d259021b9f6a32571601c9b012484497ea5a39e45562e7267a6bd02326f2` | `/tmp/ym-block-rayleigh-20261003-b.log` | `f4444ea0adacd4793beab8e163de6fe45ecad25fd1a742689c64774fb83776a4` |

Root imports are registered only, NOT aggregate-checked. No full build,
full axiom audit or baseline regeneration ran. No new sorry/axiom,
classical shortcut, resource increase, canonical field weakening or CI change.
No exact canonical displayed claim changed, so no ASCII reprint is warranted.
