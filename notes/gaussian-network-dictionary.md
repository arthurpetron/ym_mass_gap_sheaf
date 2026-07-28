# The Gaussian network dictionary of the slab and the fusion structure of the SU(2) pair moment

2026-07-28.  Work_plan §16e; code
`computations/gaussian_network_moments.py`; pins
`tests/test_gaussian_network_moments.py`; suite 48/48 green (cloud).
Stage one of the c_SU2 moment computation queued in §16d.  No value
of c_SU2 is claimed; this note banks the dictionary, two structure
theorems, the calculus gate, and the discriminating observable with
its abelian lane verified.

## 1. The dictionary (exact rationals; gated)

Gauge-fix the adapted tree.  Per su(2) component the flat limit of
the slab is the Gaussian network S(X) = |BX|^2/(4 tau) on the 16
free links (B the 20 x 16 face-boundary incidence); each coarse loop
angle is a single free link (adapted gauge — verified).  Exact
covariance data (x 2 tau per abelian component; SU(2) normalization
is 4x by the half-angle dictionary, fixed by the single-face gate):

- loop covariance  L G^{-1} L^T = [[3, 1], [1, 3]]  — GATE PASSED:
  the angle picture reproduces the flux-picture
  Qmin(n,m) = 3n^2 + 3m^2 + 2nm by Legendre duality, from
  independent linear algebra (16 x 16 rational inverse);
- face-angle variances by D4 class: tiles 79/96, perimeter walls
  79/96, interior walls 17/24 — each class exactly uniform;
- the face-loop and link-loop covariance aggregates the insertion
  assembly will consume are emitted in
  `computations/gaussian_network_results.json`.

## 2. Structure theorem 1 — the fusion-channel formula

With loop insertions as operator tilts chi_n = tr exp(i theta.J) and
Gaussian expectation (operator-ordering corrections deferred; they
are relative O(tau^2) and cannot touch the O(tau) statements):

    T[n,m]/Theta ~ sum_{J} (2J+1)
        e^{-tau [3C(n) + 3C(m) + delta_J]},
    delta_J = C(2J) - C(n) - C(m),   C(n) = n(n+2).

The abelian cross term gamma n m is REPLACED by the fusion-channel
spread.  Leading diagonal cost 3(C(n) + C(m)) — group-blind, E* = 3,
as predicted in §16b/§16c.

## 3. Structure theorem 2 — the fusion-mean identity

    sum_J (2J+1) delta_J = 2 tr(J_1 . J_2) = 0     (exact; pinned
                                                    for n, m <= 6).

The MEAN channel spread vanishes identically — the algebraic form of
the §16c realness argument.  Consequences: the SU(2) pair moment has
NO O(tau) cross correction at leading fusion order, and c_SU2 is
carried ENTIRELY by the Jacobian/BCH insertion moments plus the
finite-basis cumulant mechanism.  First surviving cross effect:
-tau^2 Var_fusion(delta)/2 in the log, with Var_fusion exact:
12 at (1,1), 32 at (1,2), 256/3 at (2,2).

## 4. The calculus gate (constants pinned)

e^{tau} E_flat[(sin phi/phi) chi_n(phi)] = d_n e^{-tau C(n)} with
phi = |theta|/2, theta isotropic R^3 Gaussian of per-component
variance 8 tau — verified to 5.4e-41 worst relative error over a
(tau, n) grid.  The (sin phi/phi) Jacobian insertion together with
the e^{tau} face normalization converts the flat (n+1)^2 into the
exact Casimir (n+1)^2 - 1: every constant of the insertion calculus
is pinned by this one identity.

## 5. The discriminating observable

The connected cross ratio X_{nm}(s) = log(T[n,m]T[0,0]/(T[n,0]T[0,m]))
separates the groups in SIGN and ORDER as tau -> 0:

    U(1):   X_11 -> -2 tau            (exact; theta kernel),
    SU(2):  X_11 -> + 6 tau^2         (prediction: Var_fusion/2;
                                       coefficient indicative until
                                       the BCH moments are assembled
                                       — they enter at the same
                                       order; the SIGN of the O(tau)
                                       term — zero — is exact).

U(1) lane VERIFIED from certified theta windows:
X_11 = -0.210720 vs -2 tau = -0.210721 at s = 9/10;
-0.020101 vs -0.020101 at s = 99/100.  The SU(2) lane is the
designated first consumer of the M -> infinity SU(2) resummation.

## 6. What remains for c_SU2 (the assembly, next)

(a) The (ii)-insertion assembly: per-face -|theta_f|^2/24 and
per-link -|X_e|^2/12 insertions correlated against the operator
tilts, using the emitted covariance aggregates; produces a
computable renormalization of the diagonal coefficient 3.
(b) The (iii)-BCH moments: cubic Gaussian moments of the commutator
corrections against the tilts — the first entry of the structure
constants, expected to carry the anti-screening sign.
(c) The finite-basis cumulant mechanism on the leading exponents
(exact, as in §16c, once (a)-(b) fix the corrected exponents).
(d) The U(1) mirror of (a)-(c) must return c_dyn = 0 exactly
(the theta representation has no polynomial corrections) — the
pipeline's refutation channel.

## 7. Honesty

Operator-ordering (BCH-of-tilts) corrections are deferred at
relative O(tau^2): O(tau) claims are safe; the tau^2 cross-ratio
COEFFICIENT is indicative.  The fusion formula is leading-order in
the insertions — (ii)/(iii) corrections dress it at O(tau).  All
verification cloud-side; Mac session-lock run owed; push of the
session's commits still owed by the user (`git push origin main`).
