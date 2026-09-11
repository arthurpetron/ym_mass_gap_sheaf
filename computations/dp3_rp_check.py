"""DP.3 — first reflection-positivity data point for the one-step blocked slab.

**Question (exponent-granularity DP.3).**  Does one blocking step on the
2x2x1 slab preserve reflection positivity in the dual (character)
coefficients, asked at EXPONENT granularity?  Concretely: is the OS Gram
matrix of reflected half-slab Wilson-loop observables, whose entries are
the DP.2 blocked-kernel s-polynomials T[n,m](s) (each entry an
exponent-aggregated object: one exact rational coefficient per
s-exponent), positive semidefinite?

**The OS pairing used (and why it is the OS one).**  The slab is the
2x2x1 brick, vertices (x,y,z), x,y in {0,1,2}, z in {0,1}
(computations/slab_blocking_kernel.py).  The reflection is

    theta : (x, y, z) |-> (x, y, 1 - z),

the plane z = 1/2.  It contains NO vertices and bisects the nine
vertical links: this is LINK reflection (Osterwalder–Seiler chessboard
reflection through a half-integer time plane), the reflection adapted to
the blocking plane of the one-step kernel.  Under theta:

  * the four top tiles (z=1 horizontal plaquettes) <-> the four bottom
    tiles; the twelve vertical faces (4 interior walls + 8 perimeter
    walls) map to themselves with orientation reversed;
  * the coarse top perimeter loop L_top <-> the bottom loop L_bot with
    the SAME in-plane orientation (a z-mirror does not reverse x-y
    traversal);
  * the owned-boundary measure prod_f K_M(U_f; s) is theta-invariant:
    K_M is a truncated heat kernel, K_M(U) = sum_{n<=M} d_n s^{C(n)}
    chi_n(U), a real class function with K_M(U^{-1}) = K_M(U).

OS observables must live strictly above the reflection plane.  The
half-configuration observables used here are

    f_n = chi_n(holonomy of L_top),      n = 0, 1, 2, ...

which depend ONLY on the four z=1 horizontal perimeter links — entirely
inside the open half-space z > 1/2.  The OS map is ANTILINEAR:
(theta f)(U) = conj( f(theta U) ).  Hence

  SU(2):  theta f_n = chi_n(L_bot)         (chi_n real, self-conjugate)
          G[n,m] := <theta(f_n) f_m> = T[n,m](s)   -- the DP.2 kernel
          entry itself, read directly as <reflected half | slab | half>.

  U(1):   theta f_n = conj(chi_n(L_bot)) = chi_{-n}(L_bot)
          G[n,m] := <theta(f_n) f_m> = T_U1[m, -n] = T_U1[-n, m]
          (module convention T_U1[top, bottom]; second equality is the
          exact z-flip symmetry T[a,b] = T[b,a], verified below).

The conjugation is NOT a pedantic choice: the check
`T_U1[1,1] != T_U1[-1,1]` passes (they differ as exact polynomials), so
for U(1) the naive unconjugated matrix T[n,m] and the OS Gram T[-n,m]
are genuinely different objects.  Only the conjugated pairing is the OS
one; the unconjugated candidate is also computed and reported, clearly
labeled, as the non-OS control.  For SU(2) all characters are real so
the two coincide and there is no ambiguity.

Normalization: <.> is the UNNORMALIZED slab integral (Haar x activities);
dividing by the partition function Z = T[0,0] > 0 rescales G by a
positive constant and cannot change PSD-ness.

Symmetry gates (computed, exact): T_su2[0,1] == T_su2[1,0];
T_U1[n,m] == T_U1[m,n] (z-flip) and T_U1[n,m] == T_U1[-n,-m] (charge
conjugation) on the whole grid — so every Gram below is symmetric as
extracted and NO symmetrization of any kind is applied.

**Checks.**  All arithmetic is exact (Fraction / integer polynomials in
s; no floats anywhere in a verdict path).

  1. leading principal minors of G as exact s-polynomials (Leibniz
     expansion), each given a sign verdict on ALL of (0,1) by the repo's
     Sturm certifier (exact_haar_network.sign_on_unit_interval) — this
     is stronger than any sample of s values;
  2. at s in {1/4, 1/2, 3/4}: rational LDL^T with the exact
     semidefinite pivot rule (pivot < 0 -> not PSD; pivot = 0 with a
     nonzero residual column -> not PSD; else recurse on the Schur
     complement) — pivot list and PSD verdict per s, plus the leading
     principal minors as exact rationals (fraction Gaussian elimination
     with row-swap sign tracking).

Truncation: activity truncation M = 1, coarse cutoff N = 3.  At M = 1
the SU(2) spin-3 row and the U(1) charge-(+-3) rows of the kernel are
identically zero (the loop cannot be dressed into the trivial channel by
spin/charge <= 1 activities on this geometry); they are kept in the Gram
as exact zero rows — a zero row is PSD-neutral (zero pivot, zero column)
and its presence is reported, not hidden.

Run:  python /home/claude/dp3/dp3_rp_check.py            (full, ~2 min)
      python /home/claude/dp3/dp3_rp_check.py --from-json (re-verify
      Gram algebra from the saved kernel polynomials, no recontraction)
"""

from __future__ import annotations

import itertools
import json
import os
import sys
import time
from fractions import Fraction
from typing import Dict, List, Tuple

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))  # repo root

from computations.exact_haar_network import sign_on_unit_interval, sp_str  # noqa: E402

Frac = Fraction
SPoly = Dict[int, Fraction]

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_PATH = os.path.join(HERE, "dp3_rp_results.json")

M_TRUNC = 1
N_SU2 = 3                      # spins 0..3 (row 3 exactly zero at M=1)
N_U1 = 3                       # charges -3..3 (rows +-3 exactly zero)
S_VALUES = [Frac(1, 4), Frac(1, 2), Frac(3, 4)]

# Basis orders (leading principal minors are taken in this order).
SU2_BASIS = [0, 1, 2, 3]
U1_BASIS = [0, 1, -1, 2, -2, 3, -3]   # informative minors first;
#                                       exact-zero rows (+-3) last


# ---------------------------------------------------------------------------
# Exact s-polynomial helpers.
# ---------------------------------------------------------------------------


def p_add(a: SPoly, b: SPoly) -> SPoly:
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, Frac(0)) + v
    return {k: v for k, v in out.items() if v}


def p_mul(a: SPoly, b: SPoly) -> SPoly:
    out: SPoly = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            k = ka + kb
            out[k] = out.get(k, Frac(0)) + va * vb
    return {k: v for k, v in out.items() if v}


def p_neg(a: SPoly) -> SPoly:
    return {k: -v for k, v in a.items()}


def p_eval(a: SPoly, s: Frac) -> Frac:
    return sum((c * s ** k for k, c in a.items()), Frac(0))


def poly_det(mat: List[List[SPoly]]) -> SPoly:
    """Exact determinant of a small matrix of s-polynomials (Leibniz)."""
    k = len(mat)
    out: SPoly = {}
    for perm in itertools.permutations(range(k)):
        sign = 1
        seen = [False] * k
        for i in range(k):          # permutation sign via cycle count
            if not seen[i]:
                j, clen = i, 0
                while not seen[j]:
                    seen[j] = True
                    j = perm[j]
                    clen += 1
                if clen % 2 == 0:
                    sign = -sign
        term = {0: Frac(sign)}
        for i in range(k):
            term = p_mul(term, mat[i][perm[i]])
            if not term:
                break
        out = p_add(out, term)
    return out


# ---------------------------------------------------------------------------
# Exact rational linear algebra at fixed s.
# ---------------------------------------------------------------------------


def rational_det(mat: List[List[Frac]]) -> Frac:
    """Fraction Gaussian elimination with row-swap sign tracking."""
    a = [row[:] for row in mat]
    k = len(a)
    det = Frac(1)
    for col in range(k):
        piv = next((r for r in range(col, k) if a[r][col] != 0), None)
        if piv is None:
            return Frac(0)
        if piv != col:
            a[col], a[piv] = a[piv], a[col]
            det = -det
        det *= a[col][col]
        inv = Frac(1) / a[col][col]
        for r in range(col + 1, k):
            f = a[r][col] * inv
            if f:
                for c in range(col, k):
                    a[r][c] -= f * a[col][c]
    return det


def ldlt_psd(mat: List[List[Frac]]):
    """Exact LDL^T with the semidefinite pivot rule (no symmetrization,
    no row pivoting: the basis order is part of the reported data).

    Returns (pivots, verdict, witness).  verdict is True iff PSD.
    Rule: at step j the pivot is the (j,j) entry of the current Schur
    complement.  pivot < 0  -> not PSD (witness: index).  pivot == 0
    with a nonzero residual column -> not PSD (a PSD matrix with zero
    diagonal has zero row/column; witness: (j, i) offending entry).
    Otherwise eliminate and continue.  All arithmetic exact."""
    a = [row[:] for row in mat]
    k = len(a)
    pivots: List[Frac] = []
    for j in range(k):
        d = a[j][j]
        pivots.append(d)
        if d < 0:
            return pivots, False, {"type": "negative_pivot", "index": j}
        if d == 0:
            for i in range(j + 1, k):
                if a[i][j] != 0:
                    return pivots, False, {
                        "type": "zero_pivot_nonzero_column",
                        "index": j,
                        "offending_row": i,
                    }
            continue
        for i in range(j + 1, k):
            lij = a[i][j] / d
            if lij:
                for c in range(j + 1, k):
                    a[i][c] -= lij * a[j][c]
    return pivots, True, None


# ---------------------------------------------------------------------------
# Kernel construction.
# ---------------------------------------------------------------------------


def build_su2(verbose: bool = True) -> Dict[Tuple[int, int], SPoly]:
    from computations.slab_blocking_kernel import kernel_entry

    T: Dict[Tuple[int, int], SPoly] = {}
    for n in range(N_SU2 + 1):
        for m in range(n, N_SU2 + 1):
            t0 = time.time()
            e = kernel_entry(n, m, M_TRUNC)
            T[(n, m)] = e
            T[(m, n)] = e
            if verbose:
                print(f"  T_su2[{n},{m}] (M={M_TRUNC}): "
                      f"{sp_str(e) if e else 0}   [{time.time()-t0:.1f}s]",
                      flush=True)
    # symmetry gate: the engine must give T[1,0] == T[0,1] exactly
    e10 = kernel_entry(1, 0, M_TRUNC)
    assert e10 == T[(0, 1)], "SU(2) z-flip symmetry gate FAILED"
    if verbose:
        print("  gate: T_su2[1,0] == T_su2[0,1] exactly (z-flip)  OK",
              flush=True)
    return T


def build_u1(verbose: bool = True) -> Dict[Tuple[int, int], SPoly]:
    from computations.dp6_u1_slab_blocking import (
        certify_kernel_basis,
        kernel_entry_u1,
    )

    assert certify_kernel_basis(), "U(1) flip-lattice certificate FAILED"
    T: Dict[Tuple[int, int], SPoly] = {}
    for n in range(-N_U1, N_U1 + 1):
        for m in range(-N_U1, N_U1 + 1):
            T[(n, m)] = kernel_entry_u1(n, m, M_TRUNC)
    # exact symmetry gates on the whole grid
    for n in range(-N_U1, N_U1 + 1):
        for m in range(-N_U1, N_U1 + 1):
            assert T[(n, m)] == T[(m, n)], "U(1) z-flip gate FAILED"
            assert T[(n, m)] == T[(-n, -m)], "U(1) charge-conj gate FAILED"
    # the conjugation in theta is material: T[1,1] != T[-1,1]
    assert T[(1, 1)] != T[(-1, 1)], (
        "expected T_U1[1,1] != T_U1[-1,1]; conjugation-necessity gate")
    if verbose:
        print("  gates: U(1) z-flip, charge-conjugation, "
              "conjugation-necessity (T[1,1] != T[-1,1])  OK", flush=True)
    return T


def gram_su2(T) -> List[List[SPoly]]:
    """OS Gram, SU(2): G[n,m] = <theta(chi_n(L_top)) chi_m(L_top)>
    = T[n,m] (real self-conjugate characters)."""
    return [[dict(T[(n, m)]) for m in SU2_BASIS] for n in SU2_BASIS]


def gram_u1(T) -> List[List[SPoly]]:
    """OS Gram, U(1): G[n,m] = <theta(chi_n(L_top)) chi_m(L_top)>
    = T_U1[-n, m] (antilinear theta conjugates the reflected charge)."""
    return [[dict(T[(-n, m)]) for m in U1_BASIS] for n in U1_BASIS]


def gram_u1_unconjugated(T) -> List[List[SPoly]]:
    """NON-OS control pairing: the raw kernel matrix T_U1[n, m] without
    the antilinear conjugation.  Reported for contrast only — this is
    NOT the Osterwalder–Schrader form."""
    return [[dict(T[(n, m)]) for m in U1_BASIS] for n in U1_BASIS]


# ---------------------------------------------------------------------------
# Analysis of one Gram matrix.
# ---------------------------------------------------------------------------


def analyze(name: str, basis, G: List[List[SPoly]], verbose=True) -> dict:
    k = len(G)
    # symmetry of the extracted Gram (must hold; nothing is symmetrized)
    sym = all(G[i][j] == G[j][i] for i in range(k) for j in range(k))
    assert sym, f"{name}: Gram not symmetric as extracted"
    zero_rows = [basis[i] for i in range(k)
                 if all(not G[i][j] for j in range(k))]

    minors_poly = []
    for size in range(1, k + 1):
        sub = [row[:size] for row in G[:size]]
        d = poly_det(sub)
        verdict = sign_on_unit_interval(d) if d else "zero"
        minors_poly.append({"size": size, "poly": d, "sturm": verdict})

    per_s = []
    for sv in S_VALUES:
        A = [[p_eval(G[i][j], sv) for j in range(k)] for i in range(k)]
        pivots, psd, witness = ldlt_psd(A)
        minors = []
        for size in range(1, k + 1):
            minors.append(rational_det([row[:size] for row in A[:size]]))
        # cross-check: rational minors must equal the polynomial minors
        for size in range(1, k + 1):
            assert minors[size - 1] == p_eval(
                minors_poly[size - 1]["poly"], sv), (
                f"{name}: minor/poly mismatch at s={sv}, size {size}")
        per_s.append({"s": sv, "pivots": pivots, "psd": psd,
                      "witness": witness, "minors": minors})

    all_s_psd = all(e["sturm"] in ("positive", "zero")
                    for e in minors_poly)
    # NOTE: nonneg leading minors alone do NOT prove PSD when zero
    # minors occur; the per-s LDL semidefinite rule is the PSD decision.
    result = {
        "name": name,
        "basis": list(basis),
        "zero_rows": zero_rows,
        "minors_poly": minors_poly,
        "per_s": per_s,
        "verdict_per_s": {str(e["s"]): bool(e["psd"]) for e in per_s},
        "all_minor_sturm_nonneg": all_s_psd,
    }
    if verbose:
        print(f"\n== {name} ==  basis order {list(basis)}"
              f"   zero rows: {zero_rows or 'none'}")
        for e in minors_poly:
            p = e["poly"]
            print(f"  leading minor {e['size']}x{e['size']}: "
                  f"{sp_str(p) if p else 0}   Sturm on (0,1): {e['sturm']}")
        for e in per_s:
            pivstr = ", ".join(str(p) for p in e["pivots"])
            print(f"  s = {e['s']}: PSD = {e['psd']}; pivots [{pivstr}]")
            if e["witness"]:
                print(f"    VIOLATION WITNESS: {e['witness']}")
            for i, mv in enumerate(e["minors"], 1):
                print(f"    minor {i}: {mv}")
    return result


# ---------------------------------------------------------------------------
# Serialization.
# ---------------------------------------------------------------------------


def _poly_json(p: SPoly):
    return {str(k): [v.numerator, v.denominator] for k, v in sorted(p.items())}


def _poly_load(d) -> SPoly:
    return {int(k): Frac(a, b) for k, (a, b) in d.items()}


def _frac_str(f: Frac) -> str:
    return f"{f.numerator}/{f.denominator}" if f.denominator != 1 \
        else str(f.numerator)


def to_json(su2_T, u1_T, analyses) -> dict:
    out = {
        "milestone": "DP.3 first RP data point (exponent granularity)",
        "date": "2026-07-25",
        "scheme": "owned-boundary slab 2x2x1, activity truncation M=1",
        "reflection": ("link reflection theta: z -> 1-z through the "
                       "plane z=1/2 (no vertices; bisects the 9 vertical "
                       "links); antilinear OS pairing "
                       "G[n,m] = <conj(f_n o theta) f_m>, "
                       "f_n = chi_n(top perimeter loop)"),
        "s_values": [str(s) for s in S_VALUES],
        "su2_kernel": {f"{n},{m}": _poly_json(su2_T[(n, m)])
                       for n in range(N_SU2 + 1)
                       for m in range(n, N_SU2 + 1)},
        "u1_kernel": {f"{n},{m}": _poly_json(u1_T[(n, m)])
                      for n in range(-N_U1, N_U1 + 1)
                      for m in range(-N_U1, N_U1 + 1)},
        "grams": {},
    }
    for a in analyses:
        out["grams"][a["name"]] = {
            "basis": a["basis"],
            "zero_rows": a["zero_rows"],
            "minors_poly": [
                {"size": e["size"], "poly": _poly_json(e["poly"]),
                 "sturm": e["sturm"]} for e in a["minors_poly"]],
            "per_s": [
                {"s": str(e["s"]),
                 "psd": bool(e["psd"]),
                 "witness": e["witness"],
                 "pivots": [_frac_str(p) for p in e["pivots"]],
                 "minors": [_frac_str(m) for m in e["minors"]]}
                for e in a["per_s"]],
            "verdict_per_s": a["verdict_per_s"],
            "all_minor_sturm_nonneg": a["all_minor_sturm_nonneg"],
        }
    return out


def load_kernels_from_json(path=JSON_PATH):
    D = json.load(open(path))
    su2_T = {}
    for key, poly in D["su2_kernel"].items():
        n, m = map(int, key.split(","))
        e = _poly_load(poly)
        su2_T[(n, m)] = e
        su2_T[(m, n)] = e
    u1_T = {}
    for key, poly in D["u1_kernel"].items():
        n, m = map(int, key.split(","))
        u1_T[(n, m)] = _poly_load(poly)
    return su2_T, u1_T, D


def run(from_json: bool = False, verbose: bool = True):
    if from_json:
        su2_T, u1_T, _ = load_kernels_from_json()
        if verbose:
            print("kernels loaded from dp3_rp_results.json "
                  "(Gram algebra re-verified, no recontraction)")
    else:
        if verbose:
            print(f"building SU(2) kernel, N={N_SU2}, M={M_TRUNC} "
                  f"(exact Haar contraction)...", flush=True)
        su2_T = build_su2(verbose)
        if verbose:
            print(f"building U(1) kernel, N={N_U1}, M={M_TRUNC} "
                  f"(exact lattice-point count)...", flush=True)
        u1_T = build_u1(verbose)

    analyses = [
        analyze("SU2_OS_Gram", SU2_BASIS, gram_su2(su2_T), verbose),
        analyze("U1_OS_Gram", U1_BASIS, gram_u1(u1_T), verbose),
        analyze("U1_unconjugated_control (NOT the OS pairing)",
                U1_BASIS, gram_u1_unconjugated(u1_T), verbose),
    ]
    return su2_T, u1_T, analyses


def main():
    from_json = "--from-json" in sys.argv
    su2_T, u1_T, analyses = run(from_json=from_json)
    if not from_json:
        with open(JSON_PATH, "w") as fh:
            json.dump(to_json(su2_T, u1_T, analyses), fh, indent=1)
        print(f"\nresults written to {JSON_PATH}")
    print("\n" + "=" * 72)
    for a in analyses:
        v = a["verdict_per_s"]
        sturm = ("all leading minors nonneg on ALL of (0,1) [Sturm]"
                 if a["all_minor_sturm_nonneg"]
                 else "SOME MINOR NOT NONNEG ON (0,1)")
        print(f"{a['name']}: PSD per s {v}; {sturm}")


if __name__ == "__main__":
    main()
