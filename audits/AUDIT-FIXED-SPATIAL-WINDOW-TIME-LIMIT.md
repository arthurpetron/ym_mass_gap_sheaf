# Two-boundary observed-window estimate and constructive time limit

Date: 2026-09-16. Classification: PROGRESS after `473b1dd`.

Whole-project goal: construct nontrivial continuum Yang--Mills on R^4 with
the required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, for the SAME theory, within the constructive axiom
gate. This increment is a fixed-nome/width/cutoff SU(2) window time limit.

## Mathematical contraction

Write u_m=T^m1, ell(h)=H[V*h], a=kineticFloor, b=kineticCap, and
q=1-a/b. For two positive certified terminal messages v,z, the existing
actual transfer sandwich constructs a bracket between Tv and Tz with
endpoints l0=(a/b)*R and u0=(b/a)*R, where R=ell(v)/ell(z)>0.
The upper certificate is the reversed lower certificate scaled by its
positive reciprocal gain; both actual mass reciprocals cancel exactly.

After s further steps, the actual bracket has positive lower endpoint
l>=l0 and width d=q^s*(u0-l0). Set kappa=(b/a)^2. The proof uses the
deliberately coarser estimate d<=q^s*u0=kappa*q^s*l0<=kappa*q^s*l.
Consequently terminalComparison compares u_(s+1+r) and u_(s+1+t),
with d<=eta*l for eta=kappa*q^s. No division by q or by l is needed.

For the SAME fixed observed window P, length L and right message u_n,

    J(h) = ell(windowMessage(L,h,P)*u_n),
    Z(h) = ell(T^L h*u_n).

These are signed rational-linear in h. An interval certificate for P
with cap C yields |J(h)|<=C*Z(h) on certified supported inputs, including
inputs with Z(h)=0. Applied to the bracket residual f-l*g, these give

    0 <= Z(f)-l*Z(g) <= eta*(l*Z(g)),
    |J(f)-l*J(g)| <= C*(Z(f)-l*Z(g)),
    |J(g)| <= C*Z(g).

The generic scalar theorem expands the signed cross determinant before
taking absolute values. Since l*Z(g)<=Z(f), cancellation against the two
positive endpoint partitions yields

    |J(f)/Z(f) - J(g)/Z(g)| <= 2*C*eta.

There is no reciprocal of the residual partition. Zero residual mass is
included, not excluded by an extra positivity premise. inputPartition_terminal
and windowRatio_input_pin identify these expressions with the previously
constructed window ratio and its unchanged partition. The initial terminal
mass ratio R disappears from the error coefficient.

## Two independent boundaries and explicit limit

For m,i>=s+1, the new left comparison gives error 2*C*kappa*q^s at
fixed L,n,P,K. Changing n to j uses the existing right error 2*C*q^s.
The two-hop rectangle theorem therefore uses

    error(s) = q^s * windowTimeCap(C),
    windowTimeCap(C) = (C+C)*(kappa+1),
    all m,n,i,j >= s+1.

The extra +1 is essential for this deliberately coarse left estimate.
The earlier observed-window audit reviewed a sharper candidate left
coefficient kappa-1 and rectangle coefficient kappa; that was a plan,
not a proved bound. The implemented statements consistently use kappa+1.

The Type-level QCauchy witness for R(t,L,t,P) stores

    M(epsilon) = 1 + geometricCutoff(q, windowTimeCap(C), epsilon).

ofQ'CauchySeq constructs the CReal. The same rectangle bound compares
R(m,L,n,P) with its actual representative at k whenever m,n,k>=s+1,
using the computed representative index QMhat>=k. It is not merely a
convergence claim about an unspecified limit. The supported-polynomial
specialization constructs the interval with C=polynomialCap(P).

## Declaration evidence

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Role |
|---|---|---|
| `ratio_bound` | `RationalPositiveResidualRatio.lean:30` | Signed cancellation with possibly zero residual mass. |
| `inputNumerator`, `inputPartition` | `BF4ExactSlabFixedSpatialWindowInput.lean:88`, `:94` | Actual same-window linear functionals. |
| `inputNumerator_add`, `inputNumerator_smul`, `inputNumerator_one` | `BF4ExactSlabFixedSpatialWindowInput.lean:120`, `:129`, `:138` | Input linearity and unchanged unobserved partition. |
| `inputPartition_nonnegative`, `inputNumerator_abs_le` | `BF4ExactSlabFixedSpatialWindowInput.lean:166`, `:201` | Certified residual bounds with no strict residual mass. |
| `inputRatio_bracket_bound` | `BF4ExactSlabFixedSpatialWindowInputComparison.lean:64` | Positive bracket implies normalized window comparison. |
| `comparisonKappa`, `comparisonEta` | `BF4ExactSlabFixedSpatialTerminalComparison.lean:81`, `:94` | Explicit nome/width-dependent coefficient and geometric error. |
| `initialComparison`, `initialComparison_upper_pin` | `BF4ExactSlabFixedSpatialTerminalComparison.lean:153`, `:172` | Actual sandwich bracket and exact endpoint ratio. |
| `terminalComparison`, `terminalComparison_lower_positive`, `terminalComparison_relative_width` | `BF4ExactSlabFixedSpatialTerminalComparison.lean:230`, `:256`, `:306` | Constructed terminal bracket, positive lower and relative width. |
| `inputPartition_terminal`, `windowRatio_input_pin` | `BF4ExactSlabFixedSpatialWindowTwoBoundary.lean:54`, `:68` | Same partition and normalized ratio pins. |
| `windowRatio_left_commonTail` | `BF4ExactSlabFixedSpatialWindowTwoBoundary.lean:116` | Left-boundary comparison with s+1 threshold. |
| `windowTimeCap`, `windowRatio_commonTail`, `polynomialWindow_commonTail` | `BF4ExactSlabFixedSpatialWindowTwoBoundary.lean:131`, `:159`, `:177` | Computed rectangle budget and all-supported-polynomial instance. |
| `windowTimeModulus`, `windowTimeCauchy`, `windowTimeLimit` | `BF4ExactSlabFixedSpatialWindowTimeLimit.lean:49`, `:54`, `:83` | Explicit modulus, Type-level witness and returned CReal. |
| `windowTime_approx_rectangular` | `BF4ExactSlabFixedSpatialWindowTimeLimit.lean:97` | Arbitrary receding boundaries approach the same representative. |
| `polynomialWindowLimit`, `polynomialWindow_approx_rectangular` | `BF4ExactSlabFixedSpatialWindowTimeLimit.lean:129`, `:143` | Actual supported-polynomial scalar limit and quantitative bound. |

## Scope and next consumer

The coefficient and time modulus are independent of late heat cutoff K
and external boundary distances. They depend on nome, spatial width and
the observable cap. No theorem here compares different heat cutoffs,
spatial widths or lattice spacings. The zero-rate case requires no special
inverse; the first-layer offset is retained. No nonzero residual assumption
or stationary positive eigenvector is inserted.

The next consumer is one consistent stationary window functional, requiring
positive linear limit laws and exact padding/shift identities. The returned
scalar for each supported P is not yet that functional. Finite redistribution
of m,L,n must not be called finite stationarity. The original ambient-lattice
window-placement theorem also remains open: chronological-chain identities
alone do not identify arbitrary geometric lattice observables.

Read-only next-step review identified the following finite identities to
prove, not results claimed at this checkpoint (write R for windowRatio):

    R(m,L+1,n,P) = R(m,L,n+1,P),
    R(m,L+1,n,lift_N(P)) = R(m+1,L,n,P).

They have the same total chain length and insertion. The intended proof
reuses `window_pairing` and `window_partition_pairing` in
`BF4ExactSlabFixedSpatialWindowPairing.lean:96` and `:124`,
`liftBoundary_add` in `SU2QuaternionHeadChainMiddleInsertion.lean:36`,
`lift_supported` in `SU2QuaternionAuxiliaryLiftAlgebra.lean:73`, and
`massRatio_congr` in `BF4ExactSlabFixedSpatialMiddleRatioPins.lean:53`.
At the limit, the comparison is with rectangles (t,t+1) and (t+1,t),
not with equal diagonal terms. The new rectangular estimate is the exact
consumer needed for this route; padding consistency remains to be checked.

Interior cutoff removal, physical reflected OS/vacuum identification,
same-operator connected correlations, completed cutoff-limit power/moment
compatibility, uniform spatial-width/spacing control, continuum QFT and the
all-group Clay target remain open. No canonical frontier field, old theorem,
literal hole or analytic premise changed.

## Verification boundary

Six focused serialized one-worker/20 GiB checks passed all 54 public gates
within {propext, Quot.sound}. The initial TwoBoundary check found only a
wrong namespace import and two nonexistent additive-positivity helper names;
existing constructive order lemmas fixed these before the accepted check.
No new literal holes, axioms or classical input. The safe-build skill kept
checks narrow and serialized. Fresh process/swap preflight preceded each
check; no competing compiler/test was found and observed swap remained
7085.19 MiB. No limits were raised.

Independent read-only mathematical review checked the same window/partition,
zero residual mass, terminal coefficient and first-layer threshold. Six
selective-root imports were added; root/full-tree/full axiom audit was NOT run.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| RationalPositiveResidualRatio | 1 | `09c03fa7976ac0ba36d9386131dadda851170a4c713e8ac35b468e0c0b944662` |
| BF4ExactSlabFixedSpatialWindowInput | 15 | `62b2a1fa32e68936c9d36828d5299bfff75115f1c5b9320278333dbc01e88048` |
| BF4ExactSlabFixedSpatialWindowInputComparison | 1 | `7c2683956b9d4b2357f69ff424d6c660775df54ec986b65f15f1d3d0a779f8b5` |
| BF4ExactSlabFixedSpatialTerminalComparison | 18 | `ec541c0a83fe0178efac3f6caeec1bfb39a60f0765066369e3afd379008d8120` |
| BF4ExactSlabFixedSpatialWindowTwoBoundary | 8 | `cdc8ad1b62714518f43f97ad8d5f0cf6e4ababb964177a1a15b59d25bad85577` |
| BF4ExactSlabFixedSpatialWindowTimeLimit | 11 | `ca88603168e5ab4b257ddbff723519263c772675993190cdb58bdeb385f1944a` |
