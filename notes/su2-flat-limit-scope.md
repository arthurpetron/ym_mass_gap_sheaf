# The SU(2) half of MD.2 — flat-limit structure and the resummation route

2026-07-28.  Companion to `notes/u1-theta-resummation.md` and
`computations/flow_asymptotic.py`.  STATUS: derivation scope, not a
theorem.  Every claim below is tagged [proved], [derived — assumptions
flagged], or [open].

## 1. What the U(1) exact solution now provides

[proved, certified]  On the one-step slab instrument the U(1)
observables near s -> 1 are, up to a certifiably bounded
exponentially small slack, the closed forms

    E*_{ab}(s) = 3 + [log P_a(s) - log P_b(s)] / (tau (C(b)-C(a))),
    P_n(s) = sum_{|m| <= N} s^{gamma n m + (alpha+1) m^2},
    alpha = 3, gamma = 2,

verified against certified windows to 1e-10 at s = 99/100, with

    E*(tau) = 3 - 4 tau + (112/5) tau^2 + O(tau^3)

and BOTH coefficients pair-independent (scheme-covariant through
second order; c1 = -gamma^2 Var_N(m)/2, N-dependent: -4/3, -4, -8 at
N = 1, 2, 3).

## 2. Where the U(1) subleading slope comes from

[proved]  The slope is driven entirely by gamma^2 — the SQUARE of the
cross term gamma n m in Qmin(n,m) = 3n^2 + 3m^2 + 2nm.  In the
Gaussian/flat picture the cross term is the linear-in-covariance
coupling of the two loop tilts:

    E[e^{i n theta_t} e^{i m theta_b}]
      = e^{-(n^2 v_t + m^2 v_b)/2 - n m c},

c the top-bottom covariance through the flip lattice: an ABELIAN
channel — the complex character e^{i m theta} has a first moment
that tilts.

## 3. The structural prediction for SU(2)

[derived — assumptions flagged]  SU(2) characters are REAL class
functions, even under X -> -X on the Lie algebra
(chi(g) = chi(g^{-1})).  For jointly Gaussian su(2)-valued loop tilts
X_t, X_b with isotropic marginals and scalar cross-covariance c:

    d/dc E[chi_n(e^{X_t}) chi_m(e^{X_b})] |_{c=0}
      = sum_i E[grad_i chi_n] E[grad_i chi_m] = 0,

because E[grad chi] over a symmetric Gaussian vanishes for an even
function.  The linear cross term — the mechanism that makes
gamma_U1 = 2 — is FORBIDDEN for SU(2).  Consequences, if the flat
limit commutes with the slab contraction [flagged assumption A1] and
the three su(2) components decouple at leading order with the same
scalar effective resistance as the abelian network [A2]:

  (i)   leading diagonal cost: E[chi_n] ~ d_n e^{-C(n) v/4} with
        C(n) = n(n+2), so the leading exponent form is
        Qmin_SU2(n,m) = 3 (C(n) + C(m)) / C(1)-normalized — i.e.
        E*_SU2(0) = 3, THE SAME as U(1): the limit is group-blind,
        as §16b anticipated;
  (ii)  gamma_SU2 = 0 at leading order: no linear cross term;
  (iii) the subleading slope c_SU2 contains NO gamma^2 basis term;
        it is pure next-order heat-kernel dynamics (BCH/curvature
        corrections, the first place the structure constants enter).

So the honest one-step discriminator, sharpened once more: compare
the MEASURED/DERIVED c_SU2 against the abelian curve — U(1) sits at
E*(tau) = 3 - 4 tau + ... with its slope fully accounted for by the
abelian cross channel; SU(2)'s slope is the first genuinely
non-abelian number of the flow.  Its SIGN is the anti-screening
statement at this order.  [open: derive or measure c_SU2.]

## 4. The SU(2) M -> infinity route (the open half of MD.2)

The obstruction: the SU(2) kernel is a character sum with varying
rational Haar-network amplitudes — no quadratic-form theta shortcut.
Two attacks, in order:

**(a) Cyclic transfer operator.**  The slab has D4-cyclic structure:
corner i couples (tile a_i, perimeter class q_i, tile a_{i+1}) with
interior wall w_i on each side.  The skeleton + tile sums should
organize as a weighted trace of a 4-fold product of ONE transfer
operator on the finite label space of (a, q, w) triples admissible at
truncation M, with 6j-network vertex weights — turning the
M -> infinity limit into convergence of a transfer kernel with
s^{C(spin)} damping.  Deliverables: the transfer factorization
theorem for the slab network (gate: reproduce
`kernel_entry_skeleton` exactly at M = 1, 2), then certified windows
at growing M with an eps_slab-grade tail bound
(|N| <= 1 unitarity-type bounds x dimension counts x s^{C} decay).

**(b) Flat-limit expansion.**  Derive (i)-(iii) with A1/A2 discharged
into finite Gaussian-moment computations: the leading order is a
Gaussian network integral on the SAME slab geometry (tensored over 3
su(2) components), and the O(tau) correction is a finite sum of
Gaussian moments against BCH commutator insertions.  This route
produces c_SU2 as an exact rational — MD.3's marginal-defect
coefficient — without any M -> infinity enumeration, and the U(1)
mirror of the same expansion must reproduce c_U1 = -4 at N = 2
[the built-in refutation channel for the expansion machinery].

## 5. Honesty

Nothing in §3 is banked: A1 (limit interchange) and A2 (component
decoupling + resistance identification) are exactly the kind of
plausible-but-unproved steps the campaign's audit rules exist for.
The U(1) side of every claim IS banked (certified windows + closed
forms).  The instrument remains the one-step, thickness-one,
anisotropic slab; iterated/isotropic upgrades are downstream.  All
verification cloud-side; Mac session-lock run and git commit
(stale index.lock) still owed.
