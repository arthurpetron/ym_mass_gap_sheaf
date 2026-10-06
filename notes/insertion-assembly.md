# Insertion-moment assembly — independent cross-check of the §16f c_SU2 assembly (reconciled)

2026-07-30.  Code `computations/insertion_moments.py` +
`computations/gaussian_network_moments.py`; pins
`tests/test_insertion_moments.py` (10/10).  RECONCILIATION NOTE:
this pipeline was built in a session that had not seen the
§16f-original assembly (`computations/c_su2_assembly.py`,
`notes/c-su2-assembly.md`) executed in a parallel session on
2026-07-28.  The two pipelines are methodologically disjoint —
this one: conditional-covariance reduction + Gaussian integration by
parts against single tilts, symbolic sympy series, closure-gated on
the exact single-face identity; the assembly: a tilted-moment engine
with epsilon-contraction tables and an exact spin cache, semigroup-
gated.  Their agreement is therefore a genuine independent
verification of the shared blocks.  The §16f-original assembly is
AUTHORITATIVE for c_SU2; this note records the cross-check and one
erratum.

## 1. Independently confirmed (exact agreement, disjoint pipelines)

- **Var_fusion(delta) = (4/3) C(n) C(m)** in closed form (via
  tr_j(J_i J_k) = delta_ik C_j d_j/3), hence the pure-fusion cross
  law kappa_2-cross = +(2/3) C(n) C(m) and X_11 = +6 tau^2 —
  matching the assembly's "cross coefficient is PURE FUSION".
- **kappa_2 diagonal block, Jacobian insertions: +139/4.**  Here:
  W = sum_e (-1/12) r_e^2 + sum_f (1/24) r_f^2 = -49/192 + 1/72 =
  -139/576 over the exact network covariances, giving
  delta log T = +(139/4) tau^2 (C(n)+C(m))-normalized — identical
  to the assembly's "Jacobians 139/4" block.
- **kappa_2 diagonal block, bare-radial/orderings: -6.**  Here from
  the bare-tilt series log(E[chi_n]/d_n) = -(C/8)a +
  (p1 C + p2 C^2)a^2 with p1 = -1/96, p2 = 0 (p2 = 0 is the
  pair-independence statement) — identical to the assembly's
  "orderings -6" block.  This term was CAUGHT here by the
  full-single-face closure gate (the assembled tau^2 coefficient
  must vanish identically at a = 8 tau against the exact identity);
  the first draft omitted it and the gate refused the pipeline.
- **Arithmetic closure of the decomposition.**  In flow-slope units:
  this module's diagonal blocks give -115/4; the assembly's BCH
  blocks (quartic +502/3, cubic-squared -4769/24, in kappa_2 units)
  give +251/8; and  -115/4 + 251/8 = +21/8 = c_dyn — the assembly's
  headline — exactly.
- The fusion-mean identity protection of cross-insertion pieces, the
  single-face insertion calculus (-(C/4) a^2 connected coefficient),
  and the U(1) mirror zeros (all three abelian insertion families
  vanish identically) — all shared.

## 2. Erratum (this session's first draft)

The first draft of this module propagated the fusion-variance term
into the flow slope with the WRONG SIGN (+(2/3)<C> instead of
-(2/3)<C>): Jensen — the variance ADDS in the log of the averaged
channel exponentials, so log T gains +tau^2 Var/2 and the slope term
is negative.  Corrected here; matches the assembly's
c_SU2(N) = 21/8 - (2/3) E_w[C(m)] = +41/40, -11/8, -183/40 at
N = 1, 2, 3.  The draft's "partial sum -99/4" framing is retracted;
the correct complete statement is the assembly's:

    c_SU2(N=2) = -11/8,   c_SU2 - c_U1 = +21/8 > 0  (exact):

the non-abelian dynamics push the one-step exponent UP relative to
the abelian control — the anti-screening statement at this order,
BANKED in §16f-original.

## 3. Incident record

Commit 9dd7139 (this session) accidentally overwrote work_plan.md
with a stale copy (deleting §16f-original through §17h, 1557 lines)
because the session's local copy predated the parallel sessions.
Restored from e72e2c8 in the follow-up commit, with this
reconciliation appended as §17i.  Lesson recorded there: sessions
must re-stage work_plan.md from the device before appending.

## 4. Provenance

The §16d flat representation of the SU(2) heat kernel is
Proposition 8.6.6 of J. Faraut, *Analysis on Lie Groups*, CUP 2008,
p. 181 (user-supplied citation; identical constants) — docstring
updated; the in-substrate 87-digit verification stands.

## 5. Where the referenced plan sections live (added 2026-10-05)

This note and its code were written in a separate clone (commits
9dd7139, 88bf720 of 2026-08-03, never pushed) and brought into this
repository on 2026-10-05. The live `work_plan.md` no longer contains
the §16f-original … §17i sections cited above; their verbatim text,
including the §17i cross-check/erratum/incident addendum, is archived
in `docs/archive/work_plan-sections-16f-17i-2026-08.md`.
