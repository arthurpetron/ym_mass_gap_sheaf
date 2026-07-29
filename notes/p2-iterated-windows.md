# P2 opened: iterated-map windows on the twice-blocked kernel (work_plan §17d)

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

## Next attack

(1) Tighten the one-step entries at 11/20-9/16 (background diagonals)
to certify the depth-2 sign there and read the s-dependence of the
collapse rate — the trajectory's certified gap curve.  (2) The
matched-flow consumer: tau'/tau windows at depth 2 under both MD.1
matchings against the §17c envelope.  (3) The thickness-2 census
(blocking-vs-stacking defect) when the recoupling evaluator lands.
