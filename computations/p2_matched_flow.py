"""P2 (continued) — the MATCHED-FLOW CONSUMER at depth 2 (work_plan
§17f; §17d/§17e next-attack item: tau'/tau under both MD.1 matchings
against the certified iterated-map windows).

THE OBJECT
----------
MD.1 (work_plan §16a) defined the observable-matched flow map by two
exact matchings on the one-step blocked slab kernel:

  D1 (separator, primary):  d_1 s'^{C(1)} = sigma(s) = lambda_1 /
      lambda_0 of the OS Gram (G = T for SU(2), G[n,m] = T[-n,m] for
      U(1)).
  D2 (pair, control):  on the flowed envelope v = T e_s,
      s'_{ab}^{C(b)-C(a)} = (v_b d_a)/(v_a d_b);  headline pair
      (0,1):  SU(2) 2 s'^3 = v_1/v_0, U(1) s' = v_1/v_0.

This module runs BOTH matchings on the certified TWO-STEP kernel
T_2 = T^2 of §17d/§17e
 and reads off the first two steps of the
matched trajectory: tau'/tau (one step) and tau''/tau (two steps),
with tau'' matched on the SAME one-step fixed-point form — i.e. s''
is the one-step-equivalent coupling of the twice-blocked map.

Three structural deliverables:

(1) **D1 depth-2 covariance is a THEOREM on composed kernels.**  For
    SU(2) the OS Gram is T itself and T is symmetric PSD (the
    entry-level OS Gram — DP.3 pairing, §17e), so lambda_i(T^2) =
    lambda_i(T)^2 with the order preserved, hence

        sigma_2(s) = sigma(s)^2      (exactly),

    and the D1 depth-2 matched coupling carries NO trajectory
    content beyond one step on the COMPOSED object:  2 s''^3 =
    sigma^2 is determined by the one-step separator.  (The echo of
    the §17d vacuity theorem: on composed kernels, even-depth
    discriminating content lives in the D2/envelope class.)  For the
    U(1) CONJUGATED Gram G = P T (P = charge flip, [P, T] = 0 by
    charge conjugation) the eigenvalues of G_2 = P T^2 are
    p_i lambda_i^2 with SIGNS p_i, so sigma(G_2) = sigma(G)^2 is NOT
    automatic — it holds iff the top two G-eigenvectors are
    parity-aligned; gated EXACTLY on the finite theta kernels.

(2) **D2 depth-2 windows — the certified two-step flow numbers.**
    The flowed envelope of the two-step kernel, v2 = T_2 e_s over
    the banked coarse basis {0, 1, 2}, gives certified rational
    windows for s''^3 = v2_1/(2 v2_0) at every §16l CERT point, from
    the SAME certified M -> infinity entry windows as §17e (a
    sharper instrument than MD.1's provisional M = 2 entries).  The
    comparison scales are exact: the 2D rule (tau'/tau = 4 per step,
    16 at depth 2) and the abelian mirror (exact theta lane at the
    same s; asymptotically E* = 3 per step, 9 at depth 2 iff the
    matched flow were semigroup-linear).

(3) **The trajectory verdict (the headline numbers).**  The matched
    coupling is nearly FROZEN under composition: s'' matched on the
    two-step kernel differs from s' by ~1e-5 relative — but the
    windows are tight enough to CERTIFY the drift: s'' < s'
    strictly (tau''/tau > tau'/tau) at s = 1/2 and 11/20 on the
    primary basis, and at 1/2, 11/20, 9/16, 4/7 on the {0,1}
    control — the SAME direction as the abelian mirror's exact
    drift (+2e-2 to +3e-2 per composed step), with a certified
    magnitude separation of ~10^3-10^4.  Scheme-covariant in sign,
    separated in magnitude: the §16 fence pattern, now at the
    trajectory level.  tau''/tau stays ~4 (NOT ~16): matching
    against the one-step fixed-point form reads the composed kernel
    as almost the SAME effective coupling — the rank-one collapse
    seen through the flow map.

SECTOR-RULE HONESTY
-------------------
MD.1's legacy sector rule keeps channels whose kernel entries are
all positive — decidable on exact truncated kernels, UNDECIDED for
the M -> infinity windows when T[0,2]/T[1,2] straddle zero.  The
envelope here is therefore computed on BOTH basis schemes:
{0, 1, 2} (straddling windows enter as certified intervals — the
primary, since every term is bounded) and {0, 1} (the control).
The matched (0,1) pair needs only v_0, v_1 > 0, certified in both
schemes.  Scheme spread is reported per point.

GATES
-----
  g_sigma_sq   sigma(A^2) = sigma(A)^2 replayed exactly through the
               charpoly/Sturm code path on a rational symmetric PSD
               matrix (the D1 theorem's code-path witness).
  g_su2_psd    the theorem on the BANKED object: the exact M = 1
               SU(2) Gram is PSD (Sturm count of negative roots is
               zero) and sigma(T^2) = sigma(T)^2 in certified
               windows.
  g_u1_parity  the U(1) conjugated-Gram verdict: sigma(G_2) vs
               sigma(G)^2 on the exact finite theta kernels (M = 2
               and M = 3 stability), banked either way.  VERDICT
               (2026-07-29): NOT reproduced — sigma_2 = 1.039e-4 <
               1.853e-4 = sigma^2 at s = 1/2, M-stable: the second
               channel of the abelian conjugated Gram is
               parity-odd, and composition damps it strictly faster
               than the square — depth-2 separator content EXISTS
               for U(1) while the SU(2) composed kernel has NONE
               (PSD theorem).  A new group-discriminating
               structural fact at the separator level, dual to the
               §17d vacuity theorem.
  g_t2_regress the generalized T_2 windows restricted to {0,1}^2
               agree exactly with p2_iterated.su2_t2_windows.
  g_mirror     the U(1) theta-lane depth-1 pair matching at
               s = 9/10 lands inside a band of the §16c exact
               asymptotic curve E* = 3 - 4 tau + O(tau^2).
  g_boundary   the SU(2) envelopes are certified positive at every
               point with s <= 3/5 (the claimed instrument range);
               61/100 and 8/13 are the reported boundary (the
               T_2(0,1)-column tails swamp the lower bounds there —
               the same l >= 9 crude wall as §17e), not failures.

Run:  python -m computations.p2_matched_flow
"""

from __future__ import annotations

import json
import math
import os
from fractions import Fraction

from computations.flow_matching import (
    build_u1,
    charpoly,
    isolate_top_two,
    kth_root_window,
    load_su2_M1,
    p_eval,
    ratio_window,
    roots_in,
    squarefree,
    strip_zero_rows,
    sturm_chain,
)
from computations.p2_iterated import (
    CERT_S,
    entry_windows,
    iv_mul,
    iv_square,
    crude_row_sums,
    su2_t2_windows,
    u_abs_bound,
    u1_entry,
    u1_t2_window,
    K_DOM,
)

Frac = Fraction
HERE = os.path.dirname(os.path.abspath(__file__))
OUT_JSON = os.path.join(HERE, "p2_matched_flow_results.json")

BASIS = (0, 1, 2)          # banked coarse basis (MD.1 sector at M=1,2)
U1_BASIS = (-2, -1, 0, 1, 2)


def cas4(k: int) -> int:
    return k * (k + 2)


def dim(k: int) -> int:
    return k + 1


# ---------------------------------------------------------------------------
# Generalized certified T_2 windows on {0, 1, 2}^2 (the §17e machinery
# extended to row/column 2; same tails, same closures).
# ---------------------------------------------------------------------------


def t2_window_full(s: Frac, ew: dict) -> dict:
    """Certified [lo, hi] for T_2[n, m], (n, m) in {0, 1, 2}^2."""
    def w(n: int, m: int):
        return ew[(min(n, m), max(n, m))]

    out = {}
    for n in BASIS:
        for m in BASIS:
            if (n, m) in out:
                continue
            lo = Frac(0)
            hi = Frac(0)
            for k in range(3):
                t = iv_square(w(n, k)) if n == m \
                    else iv_mul(w(n, k), w(k, m))
                lo += t[0]
                hi += t[1]
            tail = sum((u_abs_bound(n, k, s, ew)
                        * u_abs_bound(m, k, s, ew)
                        for k in range(3, K_DOM + 1)), Frac(0))
            _sn, _qn, vn = crude_row_sums(n, s)
            _sm, _qm, vm = crude_row_sums(m, s)
            tail += sum((a * b for a, b in
                         zip(vn[:-1], vm[:-1])), Frac(0)) \
                + 2 * vn[-1] * vm[-1]
            hi += tail
            if n != m:
                lo -= tail          # k >= 3 terms carry unknown sign
            out[(n, m)] = (lo, hi)
            out[(m, n)] = (lo, hi)
    return out


# ---------------------------------------------------------------------------
# Certified flowed envelopes and the (0,1) pair matching, both depths.
# ---------------------------------------------------------------------------


def envelope_windows(tw: dict, s: Frac, basis) -> dict:
    """v_n = sum_m T[n, m] d_m s^{C(m)} as certified intervals; tw
    maps (n, m) -> window (symmetric-key convention)."""
    out = {}
    for n in (0, 1):
        lo = Frac(0)
        hi = Frac(0)
        for m in basis:
            key = (min(n, m), max(n, m))
            wt = Frac(dim(m)) * s ** cas4(m)
            lo += tw[key][0] * wt
            hi += tw[key][1] * wt
        out[n] = (lo, hi)
    return out


def pair01_su2(v: dict) -> tuple:
    """Certified window for s'^3 = v_1 / (2 v_0) and for s' itself."""
    (lo1, hi1), (lo0, hi0) = v[1], v[0]
    assert lo0 > 0 and lo1 > 0, "envelope window not positive"
    p = (lo1 / (2 * hi0), hi1 / (2 * lo0))
    return p, kth_root_window(p, 3)


def tau_ratio(sp_win, s: Frac):
    """[lo, hi] of tau'/tau = log s' / log s (floats for reporting;
    the certified object is the rational window sp_win)."""
    ls = math.log(float(s))
    return (math.log(float(sp_win[1])) / ls,
            math.log(float(sp_win[0])) / ls)


def drift(sp1, sp2, s: Frac) -> dict:
    """The composition drift tau''/tau - tau'/tau: float window plus
    the CERTIFIED sign facts (rational-window comparisons)."""
    ls = math.log(float(s))
    lo = (math.log(float(sp2[1])) - math.log(float(sp1[0]))) / ls
    hi = (math.log(float(sp2[0])) - math.log(float(sp1[1]))) / ls
    return {"window": [lo, hi],
            "certified_positive": bool(sp2[1] < sp1[0]),
            "certified_negative": bool(sp1[1] < sp2[0])}


# ---------------------------------------------------------------------------
# The U(1) exact mirror lane (theta windows, M = infinity).
# ---------------------------------------------------------------------------


def u1_envelope(s: Frac, depth: int) -> dict:
    """v_n over the charge basis, exact certified windows; depth 1
    uses the theta entries, depth 2 the composed theta windows with
    the certified k-tail."""
    out = {}
    for n in (0, 1):
        lo = Frac(0)
        hi = Frac(0)
        for m in U1_BASIS:
            e = u1_entry(n, m, s) if depth == 1 \
                else u1_t2_window(n, m, s)
            wt = s ** (m * m)
            lo += e[0] * wt
            hi += e[1] * wt
        out[n] = (lo, hi)
    return out


def pair01_u1(v: dict) -> tuple:
    (lo1, hi1), (lo0, hi0) = v[1], v[0]
    assert lo0 > 0 and lo1 > 0
    return (lo1 / hi0, hi1 / lo0)


# ---------------------------------------------------------------------------
# Gates.
# ---------------------------------------------------------------------------


def gate_sigma_squared() -> bool:
    """sigma(A^2) = sigma(A)^2 through the charpoly/Sturm path on a
    rational symmetric PSD matrix (Gram of independent vectors)."""
    v = [[Frac(1), Frac(1, 2), Frac(1, 3)],
         [Frac(1, 2), Frac(1), Frac(1, 4)],
         [Frac(1, 5), Frac(1, 6), Frac(1)]]
    a = [[sum(v[i][k] * v[j][k] for k in range(3)) for j in range(3)]
         for i in range(3)]
    a2 = [[sum(a[i][k] * a[k][j] for k in range(3)) for j in range(3)]
          for i in range(3)]
    w0, w1, _ = isolate_top_two(a)
    q0, q1, _ = isolate_top_two(a2)
    sig = ratio_window(w1, w0)
    sig2 = ratio_window(q1, q0)
    # sigma_2 window must contain sigma^2 and be consistent
    return bool(sig2[0] <= sig[1] ** 2 and sig[0] ** 2 <= sig2[1])


def gate_su2_psd_sigma(s: Frac = Frac(1, 2)):
    """The D1 depth-2 theorem gated on the BANKED SU(2) object: the
    exact M = 1 kernel's OS Gram is PSD (Sturm count of negative
    roots = 0), and sigma(T^2) = sigma(T)^2 within the certified
    windows.  Returns (psd, equal, sigma_win, sigma2_win)."""
    T = load_su2_M1()
    basis = [0, 1, 2, 3]
    G_polys = [[dict(T[(n, m)]) for m in basis] for n in basis]
    Gr, kept, _zero = strip_zero_rows(G_polys, basis)
    A = [[p_eval(Gr[i][j], s) for j in range(len(Gr))]
         for i in range(len(Gr))]
    cp = charpoly(A)
    sf = squarefree(cp)
    chain = sturm_chain(sf)
    lead = sf[-1]
    B = 1 + max(abs(x / lead) for x in sf[:-1])
    psd = roots_in(chain, -B, Frac(0)) == 0
    A2 = [[sum(A[i][k] * A[k][j] for k in range(len(A)))
           for j in range(len(A))] for i in range(len(A))]
    w0, w1, _ = isolate_top_two(A)
    q0, q1, _ = isolate_top_two(A2)
    sig = ratio_window(w1, w0)
    sig2 = ratio_window(q1, q0)
    equal = bool(sig2[0] <= sig[1] ** 2 and sig[0] ** 2 <= sig2[1])
    return bool(psd), equal, sig, sig2


def gate_u1_parity(M: int = 2, N: int = 2):
    """sigma(G_2) vs sigma(G)^2 on the exact finite theta kernel with
    the CONJUGATED Gram G = P T; G_2 = P T^2 (finite-basis matrix
    square — the composed finite object).  Returns (equal_within,
    sigma_win, sigma2_win) with exact windows."""
    T = build_u1(N, M)
    basis = list(range(-N, N + 1))
    s = Frac(1, 2)
    G = [[p_eval(T[(-n, m)], s) for m in basis] for n in basis]
    Tm = [[p_eval(T[(n, m)], s) for m in basis] for n in basis]
    T2 = [[sum(Tm[i][k] * Tm[k][j] for k in range(len(basis)))
           for j in range(len(basis))] for i in range(len(basis))]
    P = {b: basis.index(-b) for b in basis}
    G2 = [[T2[P[basis[i]]][j] for j in range(len(basis))]
          for i in range(len(basis))]
    for i in range(len(basis)):
        for j in range(len(basis)):
            assert G[i][j] == G[j][i]
            assert G2[i][j] == G2[j][i]
    w0, w1, _ = isolate_top_two(G)
    q0, q1, _ = isolate_top_two(G2)
    sig = ratio_window(w1, w0)
    sig2 = ratio_window(q1, q0)
    equal = bool(sig2[0] <= sig[1] ** 2 and sig[0] ** 2 <= sig2[1])
    return equal, sig, sig2


def gate_mirror_curve() -> bool:
    """Depth-1 theta pair matching at s = 9/10 within a coarse band
    of the §16c exact asymptotic curve E* = 3 - 4 tau + O(tau^2)."""
    s = Frac(9, 10)
    v = u1_envelope(s, 1)
    p = pair01_u1(v)
    tr = tau_ratio(p, s)
    tau = -math.log(float(s))
    target = 3 - 4 * tau
    return bool(target - 1 < tr[0] and tr[1] < target + 1)


# ---------------------------------------------------------------------------
# main
# ---------------------------------------------------------------------------


def main() -> None:
    print("P2 matched-flow consumer at depth 2 (§17f)")
    print("=" * 66)
    g_sig = gate_sigma_squared()
    print("GATE sigma(A^2) = sigma(A)^2 (code path):",
          "PASSED" if g_sig else "FAILED")
    psd, eq_su2, ssg, ssg2 = gate_su2_psd_sigma()
    print(f"GATE SU(2) banked M=1 Gram PSD + sigma^2 covariance: "
          f"{'PASSED' if psd and eq_su2 else 'FAILED'} "
          f"(PSD {psd}, sigma2=sigma^2 {eq_su2}, "
          f"sigma ~ {float(ssg[0]):.6e})")
    par2, sg, sg2 = gate_u1_parity(2)
    par3, sg3, sg23 = gate_u1_parity(3)
    print(f"GATE U(1) conjugated-Gram parity (M=2): sigma^2 "
          f"{'REPRODUCED' if par2 else 'NOT reproduced'} "
          f"(sigma ~ {float(sg[0]):.6e}, sigma2 ~ {float(sg2[0]):.6e})")
    print(f"     M=3 stability: {'REPRODUCED' if par3 else 'NOT reproduced'}")
    g_mir = gate_mirror_curve()
    print("GATE U(1) mirror vs asymptotic curve:",
          "PASSED" if g_mir else "FAILED")

    rows = []
    g_regress = True
    g_boundary = True
    su2_range = (Frac(1, 2), Frac(11, 20), Frac(9, 16), Frac(4, 7),
                 Frac(3, 5))
    for s in CERT_S:
        tau = -math.log(float(s))
        row = {"s": str(s), "tau": tau}
        ew = entry_windows(s)
        # regression gate: restricted generalized windows == §17e
        tw = t2_window_full(s, ew)
        t2w_ref, _ = su2_t2_windows(s, ew)
        for key in ((0, 0), (0, 1), (1, 1)):
            g_regress &= tw[key] == t2w_ref[key]
        # SU(2) matched pair, both depths, both basis schemes
        for tag, basis in (("b012", BASIS), ("b01", (0, 1))):
            v1 = envelope_windows(ew, s, basis)
            v2 = envelope_windows(tw, s, basis)
            ok = all(w[0] > 0 for w in (*v1.values(), *v2.values()))
            if s in su2_range:
                g_boundary &= ok
            if not ok:
                row[tag] = {"positive": False}
                continue
            _p1, sp1 = pair01_su2(v1)
            _p2, sp2 = pair01_su2(v2)
            row[tag] = {
                "positive": True,
                "s_prime": [float(sp1[0]), float(sp1[1])],
                "s_dprime": [float(sp2[0]), float(sp2[1])],
                "tau1_ratio": tau_ratio(sp1, s),
                "tau2_ratio": tau_ratio(sp2, s),
                "drift": drift(sp1, sp2, s),
            }
        # U(1) mirror at the same s (exact theta lane)
        pu1 = pair01_u1(u1_envelope(s, 1))
        pu2 = pair01_u1(u1_envelope(s, 2))
        row["u1"] = {"tau1_ratio": tau_ratio(pu1, s),
                     "tau2_ratio": tau_ratio(pu2, s),
                     "drift": drift(pu1, pu2, s)}
        rows.append(row)
        b = row["b012"]
        print(f"s = {s}:")
        if b.get("positive"):
            t1 = b["tau1_ratio"]
            t2 = b["tau2_ratio"]
            dr = b["drift"]
            print(f"  SU2  tau'/tau in [{t1[0]:.4f}, {t1[1]:.4f}]   "
                  f"tau''/tau in [{t2[0]:.4f}, {t2[1]:.4f}]")
            print(f"       drift in [{dr['window'][0]:.3e}, "
                  f"{dr['window'][1]:.3e}]  certified>0: "
                  f"{dr['certified_positive']}  (b01 control: "
                  f"{row['b01']['drift']['certified_positive'] if row['b01'].get('positive') else 'n/a'})")
        u = row["u1"]
        print(f"  U(1) tau'/tau in [{u['tau1_ratio'][0]:.4f}, "
              f"{u['tau1_ratio'][1]:.4f}]   tau''/tau in "
              f"[{u['tau2_ratio'][0]:.4f}, {u['tau2_ratio'][1]:.4f}]"
              f"   drift ~ {u['drift']['window'][0]:.3e} "
              f"(>0: {u['drift']['certified_positive']})")
    print("GATE T2 regression vs §17e windows:",
          "PASSED" if g_regress else "FAILED")
    print("GATE SU(2) instrument range (positive envelopes on "
          "s <= 3/5):", "PASSED" if g_boundary else "FAILED")
    out = {"rows": rows,
           "gates": {"sigma_sq": bool(g_sig),
                     "su2_psd": bool(psd),
                     "su2_sigma_covariant": bool(eq_su2),
                     "u1_parity_M2": bool(par2),
                     "u1_parity_M3": bool(par3),
                     "u1_parity_sigma": [float(sg[0]), float(sg[1])],
                     "u1_parity_sigma2": [float(sg2[0]), float(sg2[1])],
                     "mirror_curve": bool(g_mir),
                     "t2_regression": bool(g_regress),
                     "boundary": bool(g_boundary)}}
    with open(OUT_JSON, "w") as fh:
        json.dump(out, fh, indent=1)
    print("ledger written")


if __name__ == "__main__":
    main()
