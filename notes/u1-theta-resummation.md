# MD.2 (U(1) half) — theta-resummation and the exact one-step flow law

2026-07-28.  Code: `computations/u1_theta_kernel.py`; pins:
`tests/test_u1_theta_kernel.py` (17/17 green with the MD.1 suite);
ledger: `computations/u1_theta_results.json`.  Work_plan §16b.

## 1. The object

Fixed-M ladders cannot reach the s -> 1 dichotomy regime (§16a: U(1)
pair01 tau'/tau still falling 19.55 -> 12.03 -> 7.88 across
M = 3, 4, 5 at s = 99/100).  But the abelian owned-boundary kernel
needs no truncation: its configuration set is exactly (particular
disk) + (rank-4 cube-flip lattice), so the M = infinity kernel is the
quadratic-form theta series

    T[n,m](s) = sum_{c in Z^4} s^{Q(c;n,m)},
    Q(c;n,m)  = c^T A c + b(n,m).c + |k0(n,m)|^2.

Exact lattice data (grid-verified, pinned):

    A = B^T B = 6 I - Adj(C_4),  spectrum {4, 6, 6, 8} (exact
    charpoly (x-4)(x-6)^2(x-8));  B^T u = (1,1,1,1) = -B^T w;
    b(n,m) = 2(n-m)(1,1,1,1);  |u|^2 = |w|^2 = 4;
    Qmin(n,m) := min_{c in R^4} Q = 3 n^2 + 3 m^2 + 2 n m.

Kernel values at rational s are certified rational windows
[partial sum over |c|_inf <= R, + tail bound], the tail bound proved
from lambda_min(A) = 4 and the shell count
(2r+1)^4 - (2r-1)^4 <= 80 r^3 — a geometric series in exact
rationals, no floats.  Gates: flip-lattice certificate; spectrum;
Qmin grid; monotone sandwich T_M(s) up to the window for
M = 3, 4, 5, 6; nested-window refinement.

## 2. The exact asymptotic law

As tau = -log s -> 0, Poisson summation gives
T[n,m](s) = Theta_0(tau) e^{-tau Qmin(n,m)} (1 + O(e^{-c/tau})) with
Theta_0 independent of (n,m).  On the flowed envelope over any
charge-conjugation-symmetric coarse basis, the mean over m kills the
cross term 2nm, and the n^2 shape of the mean matches C(n) = n^2
exactly, so EVERY D2-family observable (all pairs, and the legacy
fit) has the same limit:

    tau'/tau  ->  E*  =  alpha  =  |u|^2 - (B^T u)^T A^{-1} (B^T u)
                       =  4 - 1  =  3.

The 2D disk value 4 is screened by exactly one unit through the flip
lattice.  The limit is N-independent (any symmetric coarse cutoff)
and scheme-covariant across the D2 family — the §16 fence holds AT
the limit for this family.

## 3. The ladder (certified brackets; all three pairs 01, 02, 12)

    s        tau      pair tau'/tau brackets
    1/2      0.693    3.6520   3.0695   2.8753
    3/4      0.288    2.8031   2.7670   2.7550
    9/10     0.105    2.7809   2.7822   2.7826
    99/100   0.01005  2.9620   2.9621   2.9621     -> E* = 3

The pairs collapse onto each other as s -> 1 (covariance emerging)
and rise toward 3 as E* + O(tau); the approach is non-monotone (dip
near s ~ 0.85 — pinned).  Cross-instrument gate: at s = 1/2 the
theta value 3.65195 matches the converged fixed-M measurement 3.652
to the digit.  The §16a fixed-M values at 99/100 (19.6/12.0/7.9)
are confirmed as pure truncation artifacts; the true value is 2.962.

## 4. What is decided, and what it means

**The U(1) lane of the one-step dichotomy is decided:
tau'/tau -> 3** — not 4 (2D class), not 1 (marginal class).  Under
naive iteration tau' = 3 tau gives tau(a) ~ a^{log2 3} = a^{1.585},
which FAILS the linear floor (TS) tau(a) >= kappa a — exactly what
the discriminator demands of the gapless abelian control.  The
number the SU(2) half of MD.2 must now beat is exact: the mechanism
carries gap weight only if E*_SU2 separates BELOW E*_U1 = 3 (and
(TS)-viability under naive one-step iteration needs E*_SU2 <= 2;
marginality proper is E*_SU2 -> 1).

**Derived expectation for the SU(2) half (to be proved, not
assumed).**  In the flat (tau -> 0) limit the compact-group heat
kernel degenerates to a Gaussian on the Lie algebra, and the leading
quadratic minimization is group-blind — so SU(2) should ALSO land at
leading exponent 3, with the non-abelian content (anti-screening)
appearing in the SUBLEADING slope: E*(tau) = 3 + c_G tau + O(tau^2),
and the discriminator is c_SU2 vs c_U1.  This relocates MD.3's
"marginal-defect coefficient" one level down, to a concrete
finite computation on this instrument.  The U(1) slope is already
measurable from the ladder ((3 - 2.962)/0.01005 ~ 3.8 near tau = 0)
and exactly derivable from the theta expansion; the SU(2) analogue
needs the M -> infinity resummation of the character-sum kernel
(fixed-tile machinery + eps_slab-style tail bounds) — the open half
of MD.2 and the next attack.

## 5. Honesty box

One-step, thickness-one, ANISOTROPIC (2x2x1) blocking of the
heat-kernel theory on the DP.2 slab — an exact statement about this
instrument, not yet an iterated isotropic RG trajectory; the naive
iteration reading above is heuristic until the iterated map is
built.  The separator observable (D1) degenerates at this one-step
geometry: G(s) ~ Theta_0 (J - tau Qmin + ...) so lambda_1/lambda_0 =
O(tau) and the matched tau'/tau diverges like log(1/tau)/tau — D1
needs a tau-rescaled matching to be a dichotomy coordinate here
(recorded, not repaired).  Poisson summation enters only the
ASYMPTOTIC statement (§2); every ladder number is a certified
rational window with no transcendental input.  Cloud-container
verification only; no Mac-side run this session.
