# Positive window family and padding/translation consistency

Date: 2026-09-16. Classification: PROGRESS after `06b601f`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the required
QFT axioms and a positive physical Hamiltonian gap for every compact simple
group, on the SAME theory, within the constructive axiom gate. This increment
constructs laws of the fixed-nome/width/cutoff SU(2) polynomial window limits.

## Finite identities before limits

Write N for the spatial carrier size, u_m=T^m1, and ell(h)=H[V*h]. The
previous normalized window ratio R(m,L,n,P) retains the entire L+1-slice
insertion, original K/V action and positive denominator ell(u_(m+L)*u_n).
That denominator is independent of P. Finite coefficient algebra therefore
proves unit normalization, addition and arbitrary signed rational scaling.
Haar-carrier equality also passes through the actual input, half-open action,
partial Haar integration, terminal message and final V, with arbitrary
insertions retained. No pointwise equality replaces this carrier relation.

Multiplying a supported square certificate by the actual certified background
and integrating proves ordinary nonnegativity. More generally every supported
certificate has nonnegative expectation. The final V is present exactly once.
This is ordinary positivity, not reflection positivity.

The exact finite padding identities are

    R(m,L+1,n,P) = R(m,L,n+1,P),
    R(m,L+1,n,lift_N(P)) = R(m+1,L,n,P).

Both compare a full chain with m+L+n+1 transitions. Right padding keeps the
same literal insertion. Left padding uses the exact identity
lift_(mN)(lift_N(P))=lift_((m+1)N)(P). Apply the existing window numerator
and partition pins twice, then massRatio_congr. The extended support is
proved rather than assumed. A zero-transition window is exactly the old
middle-slice ratio. None of these identities claims finite stationarity.

## One limiting family, including different moduli

The expectation used here is the EXISTING polynomialWindowLimit. No new
chosen limit, state or functional hypothesis is introduced. Unit normalization
and certificate positivity hold on every actual CReal representative, the
latter in the transitive eventual order leEv.

Addition, signed rational homogeneity and coefficient/carrier congruence pass
by equality of the raw finite sequences and uniqueness of their limits.
This is important: polynomialCap and hence QMhat can differ between the two
inputs and their sum. The proof does not falsely equate those representatives.

For any fixed natural a,b, the prior rectangle estimate applies to the sequence
R(t+a,L,t+b,P). Both the sequence threshold and representative threshold are
the already stored explicit windowTimeModulus. Thus all these offset diagonals
converge to the SAME window limit, with no subsequence selection or new rate.

The finite padding identities compare a diagonal to (t,t+1) or (t+1,t).
Offset convergence and limit uniqueness now give

    Phi_(L+1)(P) = Phi_L(P),
    Phi_(L+1)(lift_N(P)) = Phi_L(P).

Composing the two gives one-slice translation invariance in a common enlarged
window. The L=0 limit agrees with the previously constructed slice expectation,
again by raw-sequence identity and uniqueness, not by assuming the moduli agree.

## Declaration evidence

All paths in this table have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `windowSupport_right`, `windowSupport_left` | `BF4ExactSlabFixedSpatialWindowPadding.lean:51`, `:59` | Actual support under unit padding and coordinate shift. |
| `windowRatio_pad_right`, `windowRatio_pad_left` | `BF4ExactSlabFixedSpatialWindowPadding.lean:66`, `:84` | Same-chain finite redistribution identities. |
| `windowRatio_zero` | `BF4ExactSlabFixedSpatialWindowPadding.lean:105` | Exact old middle-slice scalar at L=0. |
| `windowRatio_carrier_congr`, `windowRatio_congr` | `BF4ExactSlabFixedSpatialWindowFunctionalLaws.lean:59`, `:81` | Haar-carrier and coefficient congruence. |
| `windowRatio_one`, `windowRatio_add`, `windowRatio_smul` | `BF4ExactSlabFixedSpatialWindowFunctionalLaws.lean:89`, `:100`, `:120` | Same-partition finite rational-linear laws. |
| `windowRatio_certificate_nonnegative`, `windowRatio_square_nonnegative` | `BF4ExactSlabFixedSpatialWindowFunctionalLaws.lean:137`, `:154` | Constructed finite positivity, not OS positivity. |
| `windowTime_converges_offsets`, `polynomialWindow_converges_offsets` | `BF4ExactSlabFixedSpatialWindowState.lean:63`, `:87` | Same explicit threshold for every fixed-offset diagonal. |
| `windowLimit_one`, `windowLimit_add`, `windowLimit_smul` | `BF4ExactSlabFixedSpatialWindowState.lean:97`, `:106`, `:120` | Normalized rational-linear window limits. |
| `windowLimit_congr`, `windowLimit_carrier_congr` | `BF4ExactSlabFixedSpatialWindowState.lean:130`, `:143` | Carrier-independent value despite differing cap/modulus data. |
| `windowLimit_certificate_nonnegative`, `windowLimit_square_nonnegative` | `BF4ExactSlabFixedSpatialWindowState.lean:158`, `:169` | Actual representative positivity and eventual-order square law. |
| `windowLimit_pad_right`, `windowLimit_pad_left`, `windowLimit_shift` | `BF4ExactSlabFixedSpatialWindowState.lean:180`, `:193`, `:209` | Unit-padding and common-window one-slice translation consistency. |
| `windowLimit_zero` | `BF4ExactSlabFixedSpatialWindowState.lean:220` | Same existing positive slice functional. |

## Physical boundary and next consumer

This checkpoint supplies a normalized positive rational-linear window family
with unit-padding and one-slice-translation consistency. It does not construct
a bundled original-observable or reflected OS theory. The constants and time
moduli still depend on nome, spatial width and polynomial cap; retained heat
cutoff is fixed in each limit. No cutoff, volume or spacing estimate is added.

The earliest missing SAME-object edge identified by source review is complete
window placement into original lattice observables. There is a concrete
consumer: `original_chain_pairing` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainAction.lean:102` already
handles physical spatial FaceFactor probes at multiple times. In contrast,
`swept_middle_pairing` and `middleRatio_originalFiniteValue` in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialOriginalMiddle.lean:113` and
`:205` only pin one slice. Whole-window block embedding and probe-product
placement, then the SAME finiteValue normalization, remain to be proved.
An arbitrary supported link-coordinate polynomial is not automatically an
original gauge observable. No such substitution is made here.

Downstream, `CanonicalOSRoot.WilsonFunctionalRoot` in
`lean/YMGap/Continuum/CanonicalOSRoot.lean:53` is explicitly the ordinary
ambient state datum, not the physical OS space. The same module's opening
contract requires the reflected half-space form E((Theta a)*b); translation
invariance of an ordinary square-positive form does not supply that form or
a physical positive transfer. Its `CanonicalSchwingerLimit` at `:121` still
requires separate volume/spacing approximants and explicit convergence data.
Its `PositiveTimeOSRoot` at `:268` additionally requires supported
representatives (`representativeSupported`, `:290`), the actual reflected
form (`reflectedForm`, `:298`) and the representative/self-adjoint/positive/
contractive transfer laws (`transferRepresentative`, `:302`,
`transferSelfAdjoint`, `:313`, `transferPositive`, `:315`, and
`transferContraction`, `:316`). The window laws do not inhabit these fields.

A concrete reflected-positivity compiler does exist:
`certified_weighted_nonnegative` in
`lean/YMGap/Continuum/BF4ExactSlabSiteWeightedSquare.lean:165`. It needs a
supported one-sided insertion, a fixed-slice-local weight and that weight's
actual square certificate. The selected chain's reflection-compatible
decomposition and observable placement must supply these hypotheses; ordinary
window square positivity cannot be substituted for them.

Original multi-time observable realization, interior cutoff removal,
reflected physical OS/vacuum and same-transfer correlations, cutoff-limit
power/moment compatibility, width/spacing control, continuum QFT and all
compact simple groups remain open. No canonical field or old theorem changed.

## Verification boundary

Three focused serialized one-worker/20 GiB checks passed all 25 public gates
within {propext, Quot.sound}; windowSupport_right is axiom-free. The first
finite-law check required replacing unsupported dot notation by the existing
explicit RatPolyCoeffEqv.haarCarrier theorem. Two accepted producer checks
report an unused support argument: the algebra/certificate proofs are stronger
than their stated observable-carrier guard. The guards and docstrings remain
explicit; these are linter warnings, not failed proofs.

The safe-build skill kept verification narrow and serialized. Fresh process/
swap preflight preceded each check; no competing compiler/test process was
found, and observed swap remained 7085.19 MiB. No limits were raised. No new
literal holes, axioms, classical input or erased content-bearing witness.
Three selective-root imports were added; root/full-tree/full axiom audit was
NOT run. Independent read-only review checked the finite/limit distinction
and identified the next original-observable consumer.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| BF4ExactSlabFixedSpatialWindowPadding | 5 | `860d3072af3b760f558895a27dc4e82fe9144621f9aca7c0281c5dd1e209b314` |
| BF4ExactSlabFixedSpatialWindowFunctionalLaws | 7 | `514ca281c7339a6b21a3eb70ed85e5ff4ea051c105f123862e0928947fb852fb` |
| BF4ExactSlabFixedSpatialWindowState | 13 | `371840a744711666e5550db16d653d7f12882e9e495ebb1bff3ccadbdc3b6cba` |
