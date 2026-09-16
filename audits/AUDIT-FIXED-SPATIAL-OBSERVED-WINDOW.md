# Observed-window contraction and right-boundary forgetting

Date: 2026-09-16. Classification: PROGRESS after `133a395`.

Whole-project goal: nontrivial continuum Yang--Mills on R^4 with the
required QFT axioms and a positive physical Hamiltonian gap for every
compact simple group, for the SAME theory, within the constructive axiom
gate. This increment concerns fixed-nome/width/cutoff SU(2) time windows.

## Mathematical argument

Let N be the existing spatial slice carrier size, u_m=T^m1, and
ell(h)=H_N[V*h]. An observed polynomial P may use every coordinate of
L+1 consecutive slices, not merely factor into single-slice insertions.
Define the half-open action and its contracted message by

    A_L = product_{j<L} K(x_j,x_(j+1))*V(x_j),
    F_m = H_first_LN[(u_m*P)*A_L].

The final slice's V is deliberately absent from A_L. The exact
halfOpenAction_chain identity restores it once, through the lifted V*g.
Ordered-head Fubini then gives windowMessage_pairing. Independently,
windowMessage_iterate identifies F_m coefficientwise with T^L(u_m*P).
This identity does not assume that the starting product is one-slice
supported; the separate windowMessage_supported theorem proves that the
RESULT has one-slice support when P has the stated window support.

The generic chain_middle_pairing identity therefore retains the whole
window after m steps. Compose the remaining L+n iterates and apply actual
weighted symmetry only after contracting L steps to the supported F_m.
The complete chronological numerator becomes ell(F_m*u_n). The partition
of that SAME chain becomes ell(u_(m+L)*u_n). Each has m+L+n transitions;
the terminal spatial weight occurs once. terminalPair_positive constructs
the positive denominator at every pair of lengths, including zero.

## Certified comparison, then contraction

The new lift_carrier proof retains arbitrary inserted polynomials through
head_pairing; it does not discard off-carrier coordinates or assume
independence. Structural recursion lifts square certificates. In contrast,
enlarging a head carrier uses the existing support-guarded certificate_extend.
The positive actual K*V step and u_m thus construct the entire background
certificate on (L+1)*N coordinates.

For Interval((L+1)*N,P,C), multiply C-P and C+P by that background and
integrate its first LN coordinates. The resulting certificates are

    C*T^L(u_m) - F_m,      F_m + C*T^L(u_m).

No variable polynomial is divided out. The exact unobserved-message pin
identifies T^L(u_m)=u_(m+L). These two certificates construct a relative
bracket with endpoints -C,C. The existing actual-transfer bracket recursion
gives width q^n*(C+C). Weighted symmetry and massRatio_congr identify its
normalized mass ratio with

    R(m,L,n,P) = ell(F_m*u_n) / ell(u_(m+L)*u_n).

Nesting places R(m,L,n,P) and R(m,L,j,P) in the same s-step interval for
n,j>=s. Both order differences are bounded by q^s*(C+C). Finally the
previous polynomialInterval compiler supplies C=polynomialCap(P) for every
supported P. No additional positivity, interval or rate premise is assumed.

## Declaration evidence

All paths below have prefix `lean/YMGap/Continuum/`.

| Declaration | Module:line | Content |
|---|---|---|
| `lift_carrier`, `lift_certificate` | `SU2QuaternionHaarCertificateLift.lean:35`, `:46` | Actual coordinate shifts preserve carrier equality and constructive certificates. |
| `halfOpenAction`, `windowMessage` | `SU2QuaternionHeadWindowContraction.lean:43`, `:50` | Original half-open action and complete observed-window contraction. |
| `halfOpenAction_supported`, `windowMessage_supported` | `SU2QuaternionHeadWindowContraction.lean:62`, `:82` | Full-window and retained-slice support. |
| `halfOpenAction_chain`, `windowMessage_pairing` | `SU2QuaternionHeadWindowContraction.lean:102`, `:138` | Full chain and exact Haar pairing with final V once. |
| `windowMessage_iterate`, `windowMessage_one` | `SU2QuaternionHeadWindowContraction.lean:201`, `:209` | Actual observed/unobserved finite iterates. |
| `halfOpenAction_certificate`, `windowMessage_certificate` | `SU2QuaternionHeadWindowBounds.lean:58`, `:105` | Constructed action and integrated positive cone. |
| `windowMessage_add`, `windowMessage_smul` | `SU2QuaternionHeadWindowBounds.lean:86`, `:95` | Signed window linearity. |
| `windowMessage_upper_certificate`, `windowMessage_lower_certificate` | `SU2QuaternionHeadWindowBounds.lean:135`, `:148` | Relative bounds against the unchanged unobserved iterate. |
| `observedMessage`, `observedMessage_supported`, `window_unobserved_pin` | `BF4ExactSlabFixedSpatialWindowPairing.lean:48`, `:52`, `:61` | Concrete original K/V and terminal-message instance. |
| `window_pairing`, `window_partition_pairing` | `BF4ExactSlabFixedSpatialWindowPairing.lean:96`, `:124` | Same complete chronological numerator and partition. |
| `windowRatio`, `windowRatio_iterate` | `BF4ExactSlabFixedSpatialWindowPairing.lean:132`, `:141` | Positive actual normalization and exact bracket-ratio pin. |
| `initialWindowBracket`, `windowBracket`, `windowBracket_width` | `BF4ExactSlabFixedSpatialWindowBracket.lean:54`, `:73`, `:88` | Constructed relative bracket and exact 2Cq^n width. |
| `windowRatio_later_bounds`, `windowRatio_right_commonTail` | `BF4ExactSlabFixedSpatialWindowBracket.lean:104`, `:140` | Every later ratio and two arbitrary right distances. |
| `polynomialWindow_right_commonTail` | `BF4ExactSlabFixedSpatialWindowBracket.lean:154` | Bound for every supported window polynomial with computed cap. |

## Scope and next mathematical consumer

The checked right-tail theorem holds at the SAME m,L,P,K for both ratios.
Its error is independent of m and late K; it does not compare distinct
left boundaries. Nome and spatial width still enter q; P enters the cap.
Zero rate, empty carriers and zero window/boundary lengths remain included.
The whole-window original ambient-lattice placement is not yet pinned:
the previous single-slice geometric theorem cannot be applied by renaming P.

Independent source review identified a shorter candidate left-boundary
argument than full window reversal. This paragraph records a mathematical
plan, NOT a kernel-checked consequence. Put a=kineticFloor, b=kineticCap.
For m,i>=s+1, start with v=u_(m-s-1), z=u_(i-s-1) and R=ell(v)/ell(z)>0.
The actual transfer sandwich targets initial endpoints (a/b)*R and (b/a)*R
for (T v,T z). Existing bracket iteration/nesting would give a relative
bracket on (u_m,u_i), width delta=q^s*R*(b/a-a/b), with positive lower
endpoint l>=l0=(a/b)*R.

For the SAME fixed window and right message, write
J(h)=ell(windowMessage(L,h,P)*u_n), Z(h)=ell(T^L h*u_n).
The residual r=u_m-l*u_i and delta*u_i-r have positive certificates.
The window bounds give |J(r)|<=C*Z(r), 0<=Z(r)<=delta*Z(u_i), and
Z(u_m)>=l*Z(u_i)>0. Exact ratio algebra then targets

    |J(u_m)/Z(u_m) - J(u_i)/Z(u_i)|
      <= 2*C*delta/l <= 2*C*((b/a)^2-1)*q^s.

R cancels; no positive residual mass or uniform growing-partition floor
is needed. Adding the checked right estimate targets the rectangle budget
2*C*(b/a)^2*q^s. The remaining proof-producing steps are the initial
sandwich bracket, window-message linearity in its INPUT, and this residual
normalization estimate. Existing ratio/determinant lemmas are candidates
for reuse; this checkpoint does not assert that their hypotheses are supplied.

After two-sided convergence, unit-padding/time-shift consistency still
needs proof. Original ambient-window placement, interior heat-cutoff removal,
reflected physical OS/vacuum, connected correlations, completed cutoff-limit
power/moment compatibility, uniform spatial-width/spacing control, continuum
QFT and the all-group Clay target remain open. No canonical frontier field
or analytic premise changed.

## Verification boundary

Five focused serialized one-worker/20 GiB checks passed all 29 public gates
within {propext, Quot.sound}; halfOpenAction is axiom-free. Initial checks
exposed missing namespace opens, pattern syntax, arithmetic normalization,
a comment delimiter and an intentionally opaque weightedMass unfolding;
these were repaired before the successful checks. Only final axiom-clean
outputs are claimed here. No new literal holes, axioms or classical input.

The safe-build skill kept checks narrow and serialized. Fresh process/swap
preflight preceded every check; no competing compiler/test process was found,
and recorded swap stayed at 7085.19 MiB. No limits were raised. Independent
read-only review checked support enlargement, full-window chronology, final V
and matching partitions. Five selective-root imports were added; root/full-tree/
full axiom audit was NOT run.

Each check used `python3 scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check lean/YMGap/Continuum/<Module>.lean
--check-output lean/.lake/build/lib/lean/YMGap/Continuum/<Module>.olean
--log-file /tmp/<Module>.log`.

| Module / log basename | Gates | Final log SHA-256 |
|---|---:|---|
| SU2QuaternionHaarCertificateLift | 2 | `a882327f9d80576f655a22ea947b88eccb7c7010e12e8dd7ebdf507646d86558` |
| SU2QuaternionHeadWindowContraction | 8 | `7f89e1626dc5ec6ab533491c5208bfd0cf258766f3a4f9f5c79dfc2e085cc5b0` |
| SU2QuaternionHeadWindowBounds | 6 | `ae9fc5fa781b4469c49f2bf88deb6c858f024f8287e617d8ed7724ddfb9d1a92` |
| BF4ExactSlabFixedSpatialWindowPairing | 7 | `40514e27fe16a44a2ca8fd0773d1567e225cd6cf2d3e68c993b24f024c544d11` |
| BF4ExactSlabFixedSpatialWindowBracket | 6 | `c25303072b7027ab8ba022ef533dd12e15c2416176653dcc87d5e7219a6da573` |
