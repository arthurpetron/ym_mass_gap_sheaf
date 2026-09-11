# MD.1 — the observable-matched flow map (definition layer)

Milestone MD.1 of work_plan §16 (the marginality-dichotomy program),
executed 2026-07-28.  Code: `computations/flow_matching.py`; pins:
`tests/test_flow_matching.py`; exact ledger:
`computations/flow_matching_results.json`.  All verdict-grade
quantities are exact rationals or certified rational windows; floats
appear only as images of windows and in the legacy-fit comparison
column.

## 1. Why a definition layer

The marginality dichotomy (§16) asks whether the observable-matched
ratio tau'/tau of the one-step blocking flow tends to 4 (2D-like;
(TS) fails) or to 1+ (marginal with anti-screening; (TS) holds) as
s -> 1.  The 4-vs-1 ambiguity lives entirely in what "s'" means.  The
legacy DP.2 protocol (`dp2_measure.py`) DEFINES s' by a float
least-squares fit of log(v_n/d_n) against C(n) on the flowed envelope
v = T e_s — a projection of the blocked kernel back onto
single-plaquette form.  MD.1 replaces the fit with two exact,
observable-matched definitions and runs both, for SU(2) and U(1), in
one harness.

## 2. The two definitions

**D1 — separator matching (primary).**  The DP.3 OS pairing of the
one-step blocked slab (link reflection theta: z -> 1-z; SU(2)
G = T, U(1) G[n,m] = T[-n,m]; Haar-orthonormal coarse character
basis) is a PSD matrix of exact rationals at each rational s.  Its two
leading eigenvalues give the located one-step separator
sigma(s) = lambda_1/lambda_0 — the vacuum-orthogonalized (connected)
transfer content, the finite-matrix analogue of the located second
eigenvalue (`Continuum/LocatedSpectralGap`).  The matched coupling
solves  d_1 s'^{C(1)} = sigma(s)  against the fixed-point one-step
form diag(d_n s'^{C(n)}):

    SU(2):  2 s'^3 = sigma(s)        U(1):  s' = sigma(s).

Eigenvalues are algebraic, so the deliverable is a certified rational
window: exact characteristic polynomial (Faddeev–LeVerrier), Sturm
isolation of the top two roots, bisection, interval arithmetic for the
ratio and the C(1)-th root.  Cross-checked against an independent
float eigensolver to all printed digits.

A structural fact makes D1 the discriminating observable: the 2D
fixed-point theory on the slab geometry has a RANK-ONE pairing
(frozen-scheme gate: T_2D[n,m] = d_n d_m s^{4C(n)+4C(m)}), i.e.
lambda_1 = 0 — ZERO connected one-step transfer.  Whatever sigma(s)
measures is purely the transverse/fluctuation sector: exactly where
§15e located the non-abelian recoupling.

**D2 — pair matching on the flowed envelope (control).**  On
v = T e_s (legacy sector rule kept verbatim), the pairwise matched
coupling of channels a < b is the exact rational

    s'_{ab}^{C(b)-C(a)} = (v_b d_a) / (v_a d_b).

The (0,1) pair is the control headline; for U(1) it equals
rho_1 * s^4 with rho_1 the banked DP.6-U1 exact witness (pinned).
The pairwise ledger's spread is the exact corridor content; the
legacy float fit is carried alongside as comparison only.

## 3. Gates (all green, 2026-07-28)

g1: the legacy protocol reproduces the banked DP.2 floats to the
digit (s' = 0.034121 / corridor 1.816737 / Birkhoff 31.8848 at
s = 1/2; 0.249521 / 0.792869 / 12.5124 at s = 3/4) and the two saved
SU(2) kernel files agree entry by entry; the DP.6-U1 exact witnesses
(v_0, v_1, rho_1, rho_2 at M = 2, s = 1/2) reproduce exactly.
g2: the U(1) mirror runs on the identical slab boundary data
(imported geometry; flip-lattice certificate; z-flip, charge
conjugation, conjugation-necessity gates; agreement with the saved
DP.3 M = 1 kernels).  g3: both definitions, both groups, one ledger
per run.  Pins: 9/9 green (`tests/test_flow_matching.py`).

## 4. First ladder (float images; exact objects in the JSON)

s' under each definition ("sep" = D1, "pair01" = D2 headline,
"legacy" = float fit), against s^4:

    group M  s    | sep       pair01    legacy    s^4
    su2   1  1/4  | 1.212e-05 3.906e-03 1.120e-03 3.906e-03
    su2   2  1/4  | 1.212e-05 3.906e-03 3.906e-03 3.906e-03
    u1    3  1/4  | 2.674e-05 3.970e-03 1.299e-02 3.906e-03
    su2   1  1/2  | 3.276e-03 6.252e-02 3.412e-02 6.250e-02
    su2   2  1/2  | 3.278e-03 6.252e-02 6.263e-02 6.250e-02
    u1    3  1/2  | 1.361e-02 7.955e-02 1.262e-01 6.250e-02
    su2   1  3/4  | 1.017e-01 3.250e-01 2.495e-01 3.164e-01
    su2   2  3/4  | 1.052e-01 3.290e-01 3.359e-01 3.164e-01
    u1    3  3/4  | 1.555e-01 4.465e-01 4.518e-01 3.164e-01
    su2   1  9/10 | 2.742e-01 5.972e-01 5.154e-01 6.561e-01
    su2   2  9/10 | 2.352e-01 7.144e-01 6.877e-01 6.561e-01
    u1    3  9/10 | 1.716e-01 7.435e-01 7.384e-01 6.561e-01

tau'/tau under D2 (pair01), the dichotomy's coordinate (2D rule = 4,
marginal = 1):  SU(2) M=2: 4.000, 4.000, 3.864, 3.193;
U(1) M=3: 3.988, 3.652, 2.803, 2.813  (s = 1/4, 1/2, 3/4, 9/10).

## 5. Findings (each exact where stated)

**F1 — the banked strong-coupling sign discriminator is
truncation-borne under the envelope definition.**  At M = 1 the
spin-2 coarse channel has no 2D-disk content (the term 3 s^32 of
T[0,2] first exists at M = 2 — exact), so pairs into channel 2 sit
~100x BELOW the 2D rule while the (0,1) pair is exactly ABOVE it
(1467702248448/6005899834403585 > (1/2)^12, margin +9.7e-4
relative).  The legacy fit averaged these into the banked
s' = 0.034121 < s^4.  At matched truncation M = 2 ALL SU(2) pairs
move ABOVE the rule (1.00098, 1.01615, 1.01515 at s = 1/2, exact),
the same side as U(1) (1.27284, 13.19148, 10.36386).  The §15e
sign form of the discriminator ("SU(2) s' < s^4, U(1) s' > s^4")
does not survive matched truncation under this definition; what
survives is separation by MAGNITUDE (U(1) deviations 16x–800x the
SU(2) ones, exact ledger).

**F2 — the sign is not scheme-covariant at strong coupling.**  At
the same s, kernel, and M, the three definitions give different
defect signs (legacy below, pair01 above, separator far below).  Per
the §16 fence this refutes any fixed-strong-coupling SIGN as the
non-abelian tag; the fence's real test moves where §16 always aimed
it: the s -> 1 dichotomy class, with scheme covariance demanded of
THAT limit (MD.2).

**F3 — the separator isolates a purely transverse observable and is
M-stable.**  sigma_su2(1/2) has certified window inside
[7.0346e-8, 7.0347e-8] at M = 1 and shifts by < 0.25% at M = 2;
sigma_u1(1/2) inside [1.3612e-2, 1.3613e-2], M=2 -> 3 shift < 3e-7.
Both groups sit far below s^4 on this observable at strong coupling
(the 2D reference has sigma = 0; any nonzero value is transverse).
Exact group separation: sigma_su2 * 4 < sigma_u1 at s = 1/2 — the
SU(2) connected channel damps >4x harder than the abelian one, the
contraction-friendly direction, now on a located spectral observable
rather than a fit.

**F4 — truncation convergence degrades toward s -> 1.**  U(1)
pair01 tau'/tau at s = 9/10 moves 3.328 -> 2.813 from M = 2 to
M = 3; SU(2) M=1 -> 2 moves 4.893 -> 3.193.  Any MD.2 verdict at
the weak end needs the per-exponent finality discipline applied to
the matched quantities plus explicit M-tail bounds (eps_slab-style),
not fixed-M floats.

## 6. Honesty box

SU(2) M = 2 rows consume `dp3_m2_entries.json`, whose entries are
FINAL only below their per-entry windows (58–78); at s = 1/2 the
provisional tails weigh <= 2^-58 relative and are irrelevant, but at
s = 9/10 tail exponents weigh ~1e-3 relative and unreached
configurations could shift M = 2 values at that order — the 9/10
M = 2 row is indicative, not verdict-grade.  The separator's matched
channel is labeled by the fixed-point n = 1 channel; if the second
eigenvector migrates channels at some s, the matching target must be
re-derived (not observed on this ladder).  Nothing here touches the
dichotomy's s -> 1 limit yet: this is the definition layer.  No Mac
verification has been run this session; tests were run in the cloud
container (9/9 green) and must be re-run under the repository's
session-lock discipline on the host.

## 7. What MD.2 consumes

The harness gives MD.2 its protocol: extend the ladder toward 1
(99/100, 999/1000) with (i) U(1) at M large enough for per-digit
stability certificates, (ii) SU(2) M = 2 restricted to final windows
with explicit tail bounds, (iii) both definitions emitted per run —
the dichotomy class must agree between D1 and D2 (and any further
admissible matching) before either counts, and the U(1) lane must
separate, else the scheme family is refuted (MK-fence).  Refutations
are deliverables.
