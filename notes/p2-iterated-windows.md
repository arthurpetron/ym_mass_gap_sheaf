# P2: iterated-map windows on the twice-blocked kernel (work_plan §17d + §17e)

Companion note to `computations/p2_iterated.py`.  Executes the §17c
work order: the composition rule derived and gated, the U(1) mirror
lane exact, and the first certified trajectory-level numbers.

## The object and the composition rule

One blocking step is the banked slab kernel matrix T[n,m](s) — the
character-basis pair moments of the owned-boundary kernel.  The
iterated map is kernel composition through the shared boundary charge:
T2[n,m] = sum_k T[n,k] T[k,m], g_k = 1 by character orthonormality
(SU(2): k >= 0; U(1): k in Z).  Gates: a diagonal heat-kernel toy
composes to exact doubling (g_hk); the U(1) lane reproduces the
continuum two-step law to four digits (below).

## The structural theorem: the raw two-step sign is VACUOUS

T is real symmetric, so T2 = T^2 is a Gram matrix and Cauchy-Schwarz
forces X^(2) = log(T2[1,1]T2[0,0]/T2[0,1]^2) >= 0 for EVERY group.
The §17.4 mirror fence fires on the raw two-step cross sign — it
cannot discriminate SU(2) from U(1).  Quantified on the exact theta
kernel: at s = 1/2 the abelian one-step cross is certified NEGATIVE
(X1_U1 = -0.3564) while the two-step is certified POSITIVE
(X2_U1 = +0.02545).  Continuum form: minimizing over the shared real
charge gives Qmin_2(n,m) = 3(n^2+m^2) - (n+m)^2/6, cross coefficient
-1/3, i.e. X2_U1 -> +tau/3 as tau -> 0; the certified window at
s = 9/10 lands on tau/3 to FOUR DIGITS (3.5120e-2 vs 3.5120e-2) —
the composition convention and the sign-flip law are pinned together.
Design consequence, banked: at even iteration depth the
discriminating content of the trajectory is the MAGNITUDE /
matched-flow structure, never the sign.

## The certified SU(2) trajectory numbers

Entry windows: the §16h-16l combined assembly generalized to all
(n,m) in {0,1,2}^2 (label-less (2,2) unreached masses bounded by the
certified d-absorption prod(d) <= 4^{E/3}); k >= 3 truncation by
DomTransfer full-trace bounds (k <= 8) plus the analytic corner floor
(4^{1/3} s)^{f(k)}, f(k) = min_q (2C(q) + C(k-q)), valid on the CERT
range (4 s^3 < 1).  All exact-rational interval arithmetic; the
certified object is the rational ratio window.

* s = 1/2:  **X^(2)_SU2 in [2.04e-8, 7.16e-7], certified positive** —
  6-7 orders below the one-step X^(1) = 0.2584: the rank-one collapse
  of a strongly gapped step, certified at depth 2 (the two-step Gram
  angle is a spectral-ratio readout; composition is dominated by the
  k = 0 channel).
* **Depth-2 magnitude separation, certified**: X^(2)_SU2(1/2) <=
  7.16e-7  <  2.54e-2 = X^(2)_U1(1/2) — the SU(2) iterated kernel is
  ~5 orders closer to rank-one than the abelian mirror at the same
  coupling: the gapped-vs-Coulomb trajectory signature visible at
  depth 2, in exactly the observable class the vacuity theorem says
  carries the content.
* s = 11/20: X^(2) in [-8.8e-7, 4.07e-3] — bracketed, sign not
  certified (the one-step entry windows there are ~1e-6-wide; the
  squared connected content sits at the same scale).  s = 9/16
  similar; s = 8/13 uninformative after squaring.  The mechanical fix
  is the standing background lane (more landed diagonals tighten the
  one-step windows; every tightening squares through).

## Honesty

One composition step of the DERIVED kernels (transfer-direction
stack); re-deriving the two-step object from a thickness-2 fine-scale
census — the blocking-vs-stacking defect — is the next rung and is
precisely the §16 defect-analysis frame.  The matched-flow tau'/tau
windows at depth 2 (MD.1 matchings) are the designated consumer of
these windows, not claimed here.  The (·,2) entry windows are crude
but enter the composition only at the 1e-13 level on the CERT range.
Suite: test_p2_iterated 4/4 (10/10 with envelope3); gates g_qmin,
g_hk, g_u1_law, g_scale, g_separation all green.  Cloud only; push
owed.

## §17e: the depth-2 sign certified on the WHOLE CERT grid (SOS route)

The §17d residual (sign at 11/20, 9/16) is closed — structurally,
not by landing diagonals.  The two-step determinant is an exact sum
of squares of one-step 2x2 minors (Lagrange/Cauchy-Binet on the
Gram rows, absolutely convergent):

    det_2 = T2_00 T2_11 - T2_01^2 = sum_{k<l} M_kl^2,
    M_kl  = T[0,k] T[1,l] - T[0,l] T[1,k],

so ANY finite minor family lower-bounds det_2, and the LEADING minor
M_01 = T00 T11 - T01^2 is the one-step X11 object — already
certified positive on the §16l grid.  X^(2) = log(1 + det_2/T2_01^2)
then inherits a certified positive lower bound at every grid point:
the anticipated "background-diagonal" mechanical fix is SUPERSEDED
for the sign; landed diagonals now only sharpen magnitudes.

Certified depth-2 collapse curve (X^(2), final combined windows):

    s = 1/2    [2.077e-8, 2.148e-8]   (33x tighter than §17d)
    s = 11/20  [2.519e-7, 1.671e-5]   NEW certified sign
    s = 9/16   [4.585e-7, 1.884e-4]   NEW certified sign
    s = 4/7    [6.963e-7, 1.055e-3]   NEW point
    s = 3/5    [1.909e-6, 3.008e-1]   NEW point
    s = 61/100 [9.534e-9, --     ]    NEW point (sign only)
    s = 8/13   [2.665e-15, --    ]    sign now certified

Magnitude separation SU2 << U1 now certified at FOUR points (1/2,
11/20, 9/16, 4/7), extending the single-point §17d statement along
the anchor side: the certified onset of the gapped-vs-Coulomb
trajectory signature.

Supporting layers banked with it:

* **Entry-level OS Gram** (breaks the dom(1,3) wall): the slab
  weight factorizes across the reflection plane, so the banked §16h
  config-level OS/CS lemma sums bilinearly to |T[n,j]| <=
  sqrt(T[n,n] T[j,j]) — dom(1,3) 9.8e-5 -> 5.5e-7 at 11/20.  The
  U(1) mirror REFUTED the unconjugated form (aligned charges cost
  MORE on the slab: B^T u = -B^T w, Qmin = 3n^2+3m^2+2nm) and
  pinned the correct statement: the Gram matrix is T[nbar, m];
  SU(2) self-conjugacy closes the gap.  Gated exactly on the theta
  lane WITH a teeth check (the unconjugated form must fail).
* **Closed-form crude closure**: corner-floor convexity sandwich
  f_real <= f <= f_real + 3 (f_real = (2k^2+8k-1)/3) gives
  df >= (4k+1)/3 and a proven uniform cube-ratio (c(l+1)/c(l))^3 <=
  ((L+2)/(L+1))^3 64 (4s^3)^{ceil((4L+1)/3)}; the adaptive anchor
  L(s) (9 at 1/2 ... 67 at 8/13) makes every l >= 9 closure exact-
  segment + geometric with ratio <= 1/2 — the checked-ratio
  convention upgraded to a theorem.
* **Repairs (honesty first)**: (R1) §17d's T_2 lower bounds dropped
  possibly-negative straddling k <= 2 terms and the k >= 3 tail on
  the off-diagonal lo side (~6e-10 absolute at 11/20; no banked
  digit changes; ledger regenerated).  (R2) crude_high_k's label
  closure re-anchored sum_pow2(0) -> sum_pow2(4): ~7 orders at
  8/13.

Gates 9/9 green (g_qmin, g_hk, g_lagrange, g_oscs both lanes,
g_u1_law, g_sign full grid, g_consist, g_scale, g_separation).
Tests test_p2_iterated 7/7; test_cs_tail 6/6 unaffected.  What
binds the magnitudes now, ranked: (1) the (0,3) minor through
dom(3,3) — the first consumer for the recoupling evaluator /
landed (3,3)-class diagonals; (2) the (0,2)/(1,2) crude windows
(label-less (2,2) masses); (3) the l >= 9 crude closure only at
61/100 and 8/13.

## Next attack

(1) The matched-flow consumer: tau'/tau windows at depth 2 under
both MD.1 matchings against the §17c envelope — both instruments
now certified two-sided on 1/2..4/7.  (2) The thickness-2 census
(blocking-vs-stacking defect) when the recoupling evaluator lands;
its gate set now includes the (3,3)-class diagonal that binds the
depth-2 magnitude.  (3) P3 atlas-adequacy.
