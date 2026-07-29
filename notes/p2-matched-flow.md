# P2 matched-flow consumer at depth 2 (work_plan §17f)

Companion note to `computations/p2_matched_flow.py`.  Executes the
§17d/§17e next-attack item: tau'/tau under both MD.1 matchings on the
certified two-step kernel, U(1) mirror exact, against the §17e
iterated-map windows.

## The three structural results

**1. D1 depth-2 covariance is a theorem on composed kernels — and the
mirror breaks it.**  For SU(2) the OS Gram is T itself and T is
symmetric PSD (entry-level OS Gram, §17e; PSD machine-certified on the
banked exact M = 1 kernel by Sturm count), so lambda_i(T^2) =
lambda_i(T)^2 order-preserved and sigma_2 = sigma^2 EXACTLY: the D1
separator matching carries no trajectory content beyond one step on
the composed object (gated on the banked kernel: sigma = 7.034652e-8,
sigma_2 = sigma^2 to the window).  On the U(1) CONJUGATED Gram
G = P T the eigenvalues carry parity signs, and the exact finite
theta kernels REFUTE covariance: sigma_2 = 1.0388e-4 < 1.8531e-4 =
sigma^2 at s = 1/2, M-stable (M = 2, 3) — the abelian second channel
is parity-odd and composition damps it strictly faster than the
square.  Depth-2 separator content EXISTS for U(1) and is EMPTY for
composed SU(2): a group-discriminating structural fact dual to the
§17d vacuity theorem (there: the raw sign is trivially the same for
every group at even depth; here: the separator trajectory is trivial
for the self-conjugate group and nontrivial for the mirror).

**2. D2 pair matching at depth 2 — the first certified two-step flow
numbers.**  Flowed envelope v2 = T_2 e_s on the banked coarse basis
(primary {0,1,2}; control {0,1} — the sector membership of channel 2
is truncation-undecided for M -> infinity windows, so both schemes
run), from the SAME certified M -> infinity entry windows as §17e.
Certified windows (primary basis):

    s      tau'/tau            tau''/tau           U(1) tau'/tau -> tau''/tau
    1/2    [3.9995, 3.9995]    [3.9995, 3.9995]    3.6520 -> 3.7272
    11/20  [3.9982, 3.9984]    [3.9984, 3.9984]    3.4721 -> 3.5787
    9/16   [3.9974, 3.9979]    [3.9978, 3.9978]    3.4220 -> 3.5351
    4/7    [3.9965, 3.9978]    [3.9973, 3.9974]    3.3855 -> 3.5026
    3/5    [3.9782, 4.0110]    [3.9324, 4.0632]    3.2662 -> 3.3920

(61/100, 8/13: the SU(2) envelope lower bounds are swamped by the
T_2(0,1)-column l >= 9 crude tails — the §17e wall; the U(1) lane is
exact there: 3.2244 -> 3.3517, 3.2021 -> 3.3299.)  Consistency with
MD.1's provisional M = 2 numbers: same side of the 2D rule, same
magnitude class (tau'/tau at 1/2: 3.9995 vs M = 2's 3.9986).

**3. The trajectory verdict: a certified, scheme-covariant,
magnitude-separated composition drift.**  tau''/tau stays ~4, not
~16: matched against the one-step fixed-point form, the composed
kernel reads as almost the same effective coupling — the rank-one
collapse seen through the flow map.  But the windows are tight
enough to certify the drift tau''/tau - tau'/tau:

- SU(2), primary basis: CERTIFIED POSITIVE at 1/2 ([1.71e-5,
  1.74e-5]) and 11/20 ([3.56e-5, 1.50e-4]); window-bounded at 9/16
  ([-1.0e-4, 3.8e-4]) and 4/7.
- SU(2), {0,1} control: certified positive at 1/2, 11/20, 9/16, 4/7
  — the scheme-covariance of the sign.
- U(1), exact: +7.5e-2 at 1/2 rising to +12.8e-2 at 8/13, positive
  at every point.

Same sign, both groups, both schemes; magnitudes separated by
~4x10^3 at s = 1/2.  This is the §16 fence pattern (sign
scheme-covariant, magnitude discriminates) now holding at the
TRAJECTORY level, in exactly the observable class the vacuity
theorem licenses — and it is the first certified statement about the
matched flow's second step in the scheme family (TS) constrains.

## Gates

g_sigma_sq (code path), g_su2_psd (banked M = 1 Gram PSD +
sigma^2-covariance), g_u1_parity (VERDICT: refuted, banked),
g_mirror (theta pair vs the §16c asymptotic curve band at 9/10),
g_t2_regress (generalized T_2 windows == §17e on {0,1}^2),
g_boundary (positive envelopes on the claimed range s <= 3/5).
Tests: test_p2_matched_flow 3/3; test_flow_matching 9/9 unaffected;
test_p2_iterated modules untouched.

## Honesty

Composed DERIVED kernels (transfer-direction stack); the
thickness-2 census defect is untouched by this consumer.  The
matched objects are (0,1)-pair and separator observables on finite
coarse bases — basis-scheme dependence is reported, not hidden (the
b012/b01 spread is visible in the ledger).  tau ratios are float
images of certified rational windows; every certified claim
(drift sign, window disjointness, PSD, sigma_2 vs sigma^2) is a
rational-arithmetic comparison.  Cloud verification only.

## Next attack

(1) The drift's s-dependence: tighten 9/16 and 4/7 on the primary
basis (the (0,3)-class dom bound again — same first consumer as the
§17e magnitude ranking: the recoupling evaluator / landed
(3,3)-class diagonals).  (2) The thickness-2 census
(blocking-vs-stacking): the composed-vs-refined comparison now has
a certified target to hit — T_2-composed windows AND matched-flow
drift.  (3) P3 atlas-adequacy with both instruments.
