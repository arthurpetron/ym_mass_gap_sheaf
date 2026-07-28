# The c_SU2 assembly — MD.3's marginal-defect coefficient as an exact rational

2026-07-28.  Work_plan §16f; code `computations/c_su2_assembly.py`;
pins `tests/test_c_su2_assembly.py`; ledger
`computations/c_su2_assembly_results.json`.  Executes the §16e queue
(a)-(d): the (ii)-insertion assembly, the (iii)-BCH cubic moments,
the finite-basis cumulants, and the U(1) mirror gate — INCLUDING the
operator-ordering terms §16e deferred, which enter at exactly the
order c_SU2 lives at and are here computed, not deferred.

## 1. The engine

Per su(2) triple, the flat limit of the slab pair moment is

    T[n,m] = Z(tau) e^{F tau} tr_{V_n (x) V_m}
             E[ e^{iL} exp( q - V_3 - V_4 ) ],

L = theta_t.J_1 + theta_b.J_2 the loop tilts (single free links,
adapted gauge), q the phi/sin(phi) heat-kernel Jacobians plus the
(sin u/u)^2 link Haar densities, V_3 = sum_f theta_f.Delta_f^(2)/(8 tau)
and V_4 = sum_f [|Delta_f^(2)|^2 + 2 theta_f.Delta_f^(3)]/(16 tau)
the BCH non-closure of the face-ordered link products (commutator =
cross product), Gaussian covariance 8 tau G^{-1} per component (the
§16e dictionary).  The engine reduces every needed tilted moment —
E[L^2], E[L^4] (ordered words), E[q_2 L^2], E[V_4 L^2],
E[V_3^2 L^2], E[V_3 L^3] — to exact-rational J-word tables by Wick
contraction (epsilon-epsilon contractions via precomputed isotropic
patterns; E[det det] = 6 det(Cov)), then trace-evaluates per (n, m)
with an exact complex-rational spin-matrix cache.  E[V_3 L] = 0
exactly (parity), asserted.  The series

    S(n,m) = 1 + tau s_1(n,m) + tau^2 s_2(n,m)

is exact through tau^2 in its (n,m)-dependent part; discarded terms
are J-free (normalization), odd-J (trace zero), or O(tau^3).

## 2. The gates (all exact, all green)

- **Semigroup chains (decisive).**  On the 1-, 2-, 3-link chain
  networks the heat-kernel semigroup forces
  log(T[n]/(d_n T[0])) = -k tau C(n) EXACTLY; the engine's entire
  tau^2 connected coefficient vanishes identically — one identity
  exercising Jacobians, V_3, V_4, orderings, and normalization
  together.  Any sign or factor error anywhere breaks it.
- **BCH gate.**  The derived Delta^(2)/Delta^(3) (graded recursion,
  pure rational) against mpmath 2x2 matrix logs: passes for 2-, 3-,
  4-factor products.
- **U(1) mirror (§16e (d)).**  The identical engine at one abelian
  component: kappa_2 = 0 identically — **c_dyn^{U(1)} = 0 exactly**
  — and the identical flow assembly reproduces the banked
  c_1 = -4 at N = 2 (all pairs).  The refutation channel does not
  fire.
- **Structure.**  s_1 = const - 3(C(n)+C(m)) exactly (E* -> 3,
  group-blind, again); the assembled series exactly real; the
  polynomial fit below exact on the 4x4 grid and on held-out n = 4.

## 3. The result

    kappa_2(n,m) - kappa_2(0,0)
        = -(21/8) (C(n) + C(m)) + (2/3) C(n) C(m)      (EXACT),

kappa_2 the tau^2 connected coefficient of log T[n,m].  No C^2
terms: the D2 pair family stays scheme-covariant at this order —
pair-independence of the slope is a theorem of the fit, not an
assumption.  Consequences:

- **Cross coefficient = pure fusion.**  (2/3) C(n) C(m) =
  Var_fusion(delta)/2 exactly: the Jacobian/BCH/ordering machinery
  does NOT touch the cross channel.  The discriminating observable is
  now exact at this order:

      X_nm = (2/3) C(n) C(m) tau^2 + O(tau^3),   X_11 = +6 tau^2,

  upgrading §16e's "indicative" +6 to an exact coefficient.  Checked
  against the exact banked M=2 SU(2) kernel: T[1,1]T[0,0] > T[0,1]^2
  (exact rational, several s), X_11/tau^2 rising through ~6 on
  s in [3/4, 17/20] before fixed-M truncation bites (the §16a
  protocol discovery says fixed M cannot reach s -> 1; consistent).
- **Diagonal dynamical defect.**

      c_dyn = +21/8,

  the coefficient by which the non-abelian dynamics push the
  one-step exponent, per unit Casimir, relative to the abelian
  mirror (whose c_dyn = 0 is gated, not assumed).  Block attribution
  (each exact): orderings -6, Jacobians +139/4, BCH-quartic +502/3,
  BCH-cubic-squared -4769/24, epsilon-linear cubic moment 0 — a
  delicate cancellation certified by the chain gates.
- **Flow slopes.**  E*(tau) = 3 + c_SU2(N) tau with

      c_SU2(N) = 21/8 - (2/3) E_w[C(m)],   w_m ~ d_m^2, m <= N:
      N = 1: +41/40,   N = 2: -11/8,   N = 3: -183/40,

  pair-independent at every N (gated).  The N-dependence is basis
  bookkeeping exactly parallel to U(1)'s -4/3, -4, -8 (§16c); the
  basis-free content is c_dyn and the cross coefficient.
- **The matched-basis comparison (MD.3's number).**  At the standard
  basis N = 2 the SU(2) fusion-basis term is -(2/3)*6 = -4 — equal
  to U(1)'s entire slope — so

      c_SU2 - c_U1 = +21/8    exactly, at matched basis N = 2:

  the first genuinely non-abelian number of the flow.  Its sign is
  POSITIVE: the non-abelian correction pushes E* UP — away from
  marginality, toward the gapped/2D class — relative to the gapless
  abelian control on the same instrument with the same basis.  This
  is the anti-screening statement at this order, now an exact
  rational with no measured input.

## 4. Honesty

One-step, thickness-one, anisotropic slab instrument; tau-slope of
the D2 family at s -> 1; iterated/isotropic upgrades downstream.
The flat-limit dictionary inherits §16c/§16d's exponentially small
image and theta-separation slack — certified rational for U(1),
numerically gated (41-87 digits) for SU(2); a certified-rational
SU(2) slack bound is owed by whichever step first consumes c_dyn in
a verdict.  tau^3 coefficients are outside this computation.  The
M=2 kernel cross-check is a sign/consistency gate, not a
certificate (fixed-M cannot reach the asymptotic regime).  A2
(component decoupling) is DISCHARGED at this order by construction
(the engine computes the coupled 3-component integral exactly); A1
(limit interchange) remains flagged as before.  Cloud verification
only; Mac session-lock run owed; push owed by Arthur
(`git push origin main`).
